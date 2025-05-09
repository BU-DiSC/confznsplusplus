#include "qemu/osdep.h"
#include "hw/qdev-properties.h"

#include "./nvme.h"

#define NVME_SPEC_VER (0x00010400)

static void nvme_clear_ctrl(FemuCtrl *n, bool shutdown)
{
    /* Coperd: pause nvme poller at earliest convenience */
    n->dataplane_started = false;

    if (shutdown) {
        femu_debug("shutting down NVMe Controller ...\n");
    } else {
        femu_debug("disabling NVMe Controller ...\n");
    }

    if (shutdown) {
        femu_debug("%s,clear_guest_notifier\n", __func__);
        nvme_clear_virq(n);
    }

    for (int i = 0; i <= n->num_io_queues; i++) {
        if (n->sq[i] != NULL) {
            nvme_free_sq(n->sq[i], n);
        }
    }
    for (int i = 0; i <= n->num_io_queues; i++) {
        if (n->cq[i] != NULL) {
            nvme_free_cq(n->cq[i], n);
        }
    }

    n->bar.cc = 0;
    n->features.temp_thresh = 0x14d;
    n->temp_warn_issued = 0;
    n->dbs_addr = 0;
    n->dbs_addr_hva = 0;
    n->eis_addr = 0;
    n->eis_addr_hva = 0;
}

static int nvme_start_ctrl(FemuCtrl *n)
{
    uint32_t page_bits = NVME_CC_MPS(n->bar.cc) + 12;
    uint32_t page_size = 1 << page_bits;

    if (n->cq[0] || n->sq[0] || !n->bar.asq || !n->bar.acq ||
        n->bar.asq & (page_size - 1) || n->bar.acq & (page_size - 1) ||
        NVME_CC_MPS(n->bar.cc) < NVME_CAP_MPSMIN(n->bar.cap) ||
        NVME_CC_MPS(n->bar.cc) > NVME_CAP_MPSMAX(n->bar.cap) ||
        NVME_CC_IOCQES(n->bar.cc) < NVME_CTRL_CQES_MIN(n->id_ctrl.cqes) ||
        NVME_CC_IOCQES(n->bar.cc) > NVME_CTRL_CQES_MAX(n->id_ctrl.cqes) ||
        NVME_CC_IOSQES(n->bar.cc) < NVME_CTRL_SQES_MIN(n->id_ctrl.sqes) ||
        NVME_CC_IOSQES(n->bar.cc) > NVME_CTRL_SQES_MAX(n->id_ctrl.sqes) ||
        !NVME_AQA_ASQS(n->bar.aqa) || NVME_AQA_ASQS(n->bar.aqa) > 4095 ||
        !NVME_AQA_ACQS(n->bar.aqa) || NVME_AQA_ACQS(n->bar.aqa) > 4095) {
        return -1;
    }

    n->page_bits = page_bits;
    n->page_size = 1 << n->page_bits;
    n->max_prp_ents = n->page_size / sizeof(uint64_t);
    n->cqe_size = 1 << NVME_CC_IOCQES(n->bar.cc);
    n->sqe_size = 1 << NVME_CC_IOSQES(n->bar.cc);

    nvme_init_cq(&n->admin_cq, n, n->bar.acq, 0, 0, NVME_AQA_ACQS(n->bar.aqa) +
                 1, 1, 1);
    nvme_init_sq(&n->admin_sq, n, n->bar.asq, 0, 0, NVME_AQA_ASQS(n->bar.aqa) +
                 1, NVME_Q_PRIO_HIGH, 1);

    /* Currently only used by FEMU ZNS extension */
    if (n->ext_ops.start_ctrl) {
        n->ext_ops.start_ctrl(n);
    }

    return 0;
}

static void nvme_write_bar(FemuCtrl *n, hwaddr offset, uint64_t data, unsigned size)
{
    switch (offset) {
    case 0xc:
        n->bar.intms |= data & 0xffffffff;
        n->bar.intmc = n->bar.intms;
        break;
    case 0x10:
        n->bar.intms &= ~(data & 0xffffffff);
        n->bar.intmc = n->bar.intms;
        break;
    case 0x14:
        /* If first sending data, then sending enable bit */
        if (!NVME_CC_EN(data) && !NVME_CC_EN(n->bar.cc) &&
                !NVME_CC_SHN(data) && !NVME_CC_SHN(n->bar.cc))
        {
            n->bar.cc = data;
        }

        if (NVME_CC_EN(data) && !NVME_CC_EN(n->bar.cc)) {
            n->bar.cc = data;
            if (nvme_start_ctrl(n)) {
                n->bar.csts = NVME_CSTS_FAILED;
            } else {
                n->bar.csts = NVME_CSTS_READY;
            }
        } else if (!NVME_CC_EN(data) && NVME_CC_EN(n->bar.cc)) {
            nvme_clear_ctrl(n, false);
            n->bar.csts &= ~NVME_CSTS_READY;
        }
        if (NVME_CC_SHN(data) && !(NVME_CC_SHN(n->bar.cc))) {
            nvme_clear_ctrl(n, true);
            n->bar.cc = data;
            n->bar.csts |= NVME_CSTS_SHST_COMPLETE;
        } else if (!NVME_CC_SHN(data) && NVME_CC_SHN(n->bar.cc)) {
            n->bar.csts &= ~NVME_CSTS_SHST_COMPLETE;
            n->bar.cc = data;
        }
        break;
    case 0x24:
        n->bar.aqa = data & 0xffffffff;
        break;
    case 0x28:
        n->bar.asq = data;
        break;
    case 0x2c:
        n->bar.asq |= data << 32;
        break;
    case 0x30:
        n->bar.acq = data;
        break;
    case 0x34:
        n->bar.acq |= data << 32;
        break;
    default:
        break;
    }
}

static uint64_t nvme_mmio_read(void *opaque, hwaddr addr, unsigned size)
{
    FemuCtrl *n = (FemuCtrl *)opaque;
    uint8_t *ptr = (uint8_t *)&n->bar;
    uint64_t val = 0;

    if (addr < sizeof(n->bar)) {
        memcpy(&val, ptr + addr, size);
    }

    return val;
}

static void nvme_process_db_admin(FemuCtrl *n, hwaddr addr, int val)
{
    uint32_t qid;
    uint16_t new_val = val & 0xffff;
    NvmeSQueue *sq;
    //inho debug
    //femu_err("Seq 1 nvme_process_db_admin femu.c:146\n");
    if (((addr - 0x1000) >> (2 + n->db_stride)) & 1) {
        NvmeCQueue *cq;

        qid = ((addr - (0x1000 + (1 << (2 + n->db_stride)))) >> (3 +
                                                                 n->db_stride));
        if (nvme_check_cqid(n, qid)) {
            return;
        }

        cq = n->cq[qid];
        if (new_val >= cq->size) {
            return;
        }

        cq->head = new_val;

        if (cq->tail != cq->head) {
            nvme_isr_notify_admin(cq);
        }
    } else {
        qid = (addr - 0x1000) >> (3 + n->db_stride);
        if (nvme_check_sqid(n, qid)) {
            return;
        }
        sq = n->sq[qid];
        if (new_val >= sq->size) {
            return;
        }

        sq->tail = new_val;
        nvme_process_sq_admin(sq);
    }
}

static void nvme_process_db_io(FemuCtrl *n, hwaddr addr, int val)
{
    uint32_t qid;
    uint16_t new_val = val & 0xffff;
    NvmeSQueue *sq;

    if (n->dataplane_started) {
        return;
    }

    if (addr & ((1 << (2 + n->db_stride)) - 1)) {
        return;
    }

    if (((addr - 0x1000) >> (2 + n->db_stride)) & 1) {
        NvmeCQueue *cq;

        qid = ((addr - (0x1000 + (1 << (2 + n->db_stride)))) >> (3 +
                                                                 n->db_stride));
        if (nvme_check_cqid(n, qid)) {
            return;
        }

        cq = n->cq[qid];
        if (new_val >= cq->size) {
            return;
        }

        if (!cq->db_addr) {
            cq->head = new_val;
        }

        if (cq->tail != cq->head) {
            nvme_isr_notify_io(cq);
        }
    } else {
        qid = (addr - 0x1000) >> (3 + n->db_stride);
        if (nvme_check_sqid(n, qid)) {
            return;
        }
        sq = n->sq[qid];
        if (new_val >= sq->size) {
            return;
        }

        if (!sq->db_addr) {
            sq->tail = new_val;
        }
    }
}

static void nvme_mmio_write(void *opaque, hwaddr addr, uint64_t data, unsigned size)
{
    FemuCtrl *n = (FemuCtrl *)opaque;
    if (addr < sizeof(n->bar)) {
        nvme_write_bar(n, addr, data, size);
    } else if (addr >= 0x1000 && addr < 0x1008) {
        nvme_process_db_admin(n, addr, data);
    } else {
        nvme_process_db_io(n, addr, data);
    }
}

static void nvme_cmb_write(void *opaque, hwaddr addr, uint64_t data, unsigned size)
{
    FemuCtrl *n = (FemuCtrl *)opaque;

    memcpy(&n->cmbuf[addr], &data, size);
}

static uint64_t nvme_cmb_read(void *opaque, hwaddr addr, unsigned size)
{
    uint64_t val;
    FemuCtrl *n = (FemuCtrl *)opaque;

    memcpy(&val, &n->cmbuf[addr], size);

    return val;
}

static const MemoryRegionOps nvme_cmb_ops = {
    .read = nvme_cmb_read,
    .write = nvme_cmb_write,
    .endianness = DEVICE_LITTLE_ENDIAN,
    .impl = {
        .min_access_size = 2,
        .max_access_size = 8,
    },
};

static const MemoryRegionOps nvme_mmio_ops = {
    .read = nvme_mmio_read,
    .write = nvme_mmio_write,
    .endianness = DEVICE_LITTLE_ENDIAN,
    .impl = {
        .min_access_size = 2,
        .max_access_size = 8,
    },
};

static int nvme_check_constraints(FemuCtrl *n)
{
    if ((n->num_namespaces == 0 || n->num_namespaces > NVME_MAX_NUM_NAMESPACES)
        || (n->num_io_queues < 1 || n->num_io_queues > NVME_MAX_QS) ||
        (n->db_stride > NVME_MAX_STRIDE) ||
        (n->max_q_ents < 1) ||
        (n->max_sqes > NVME_MAX_QUEUE_ES || n->max_cqes > NVME_MAX_QUEUE_ES ||
         n->max_sqes < NVME_MIN_SQUEUE_ES || n->max_cqes < NVME_MIN_CQUEUE_ES) ||
        (n->vwc > 1 || n->intc > 1 || n->cqr > 1 || n->extended > 1) ||
        (n->nlbaf > 16) ||
        (n->lba_index >= n->nlbaf) ||
        (n->meta && !n->mc) ||
        (n->extended && !(NVME_ID_NS_MC_EXTENDED(n->mc))) ||
        (!n->extended && n->meta && !(NVME_ID_NS_MC_SEPARATE(n->mc))) ||
        (n->dps && n->meta < 8) ||
        (n->dps && ((n->dps & DPS_FIRST_EIGHT) &&
                    !NVME_ID_NS_DPC_FIRST_EIGHT(n->dpc))) ||
        (n->dps && !(n->dps & DPS_FIRST_EIGHT) &&
         !NVME_ID_NS_DPC_LAST_EIGHT(n->dpc)) ||
        (n->dps & DPS_TYPE_MASK && !((n->dpc & NVME_ID_NS_DPC_TYPE_MASK) &
                                     (1 << ((n->dps & DPS_TYPE_MASK) - 1)))) ||
        (n->mpsmax > 0xf || n->mpsmax > n->mpsmin) ||
        (n->oacs & ~(NVME_OACS_FORMAT)) ||
        (n->oncs & ~(NVME_ONCS_COMPARE | NVME_ONCS_WRITE_UNCORR |
                     NVME_ONCS_DSM | NVME_ONCS_WRITE_ZEROS))) {
                         return -1;
     }

    return 0;
}

static void nvme_ns_init_identify(FemuCtrl *n, NvmeIdNs *id_ns)
{
    int npdg;

    /* NSFEAT Bit 3: Support the Deallocated or Unwritten Logical Block error */
    id_ns->nsfeat        |= (0x4 | 0x10);
    id_ns->nlbaf         = n->nlbaf - 1;
    id_ns->flbas         = n->lba_index | (n->extended << 4);
    id_ns->mc            = n->mc;
    id_ns->dpc           = n->dpc;
    id_ns->dps           = n->dps;
    id_ns->dlfeat        = 0x9;
    id_ns->lbaf[0].lbads = 9;
    id_ns->lbaf[0].ms    = 0;

    npdg = 1;
    id_ns->npda = id_ns->npdg = npdg - 1;

    for (int i = 0; i < n->nlbaf; i++) {
        id_ns->lbaf[i].lbads = BDRV_SECTOR_BITS + i;
        id_ns->lbaf[i].ms    = cpu_to_le16(n->meta);
    }
}

static int nvme_init_namespace(FemuCtrl *n, NvmeNamespace *ns, Error **errp)
{
    NvmeIdNs *id_ns = &ns->id_ns;
    uint64_t num_blks;
    int lba_index;

    nvme_ns_init_identify(n, id_ns);

    lba_index = NVME_ID_NS_FLBAS_INDEX(ns->id_ns.flbas);
    num_blks = n->ns_size / ((1 << id_ns->lbaf[lba_index].lbads));
    id_ns->nuse = id_ns->ncap = id_ns->nsze = cpu_to_le64(num_blks);

    n->csi = NVME_CSI_NVM;
    ns->ctrl = n;
    ns->ns_blks = ns_blks(ns, lba_index);
    ns->util = bitmap_new(num_blks);
    ns->uncorrectable = bitmap_new(num_blks);

    return 0;
}

static int nvme_init_namespaces(FemuCtrl *n, Error **errp)
{
    /* FIXME: FEMU only supports 1 namesapce now */
    assert(n->num_namespaces == 1);

    for (int i = 0; i < n->num_namespaces; i++) {
        NvmeNamespace *ns = &n->namespaces[i];
        ns->size = n->ns_size;
        ns->start_block = i * n->ns_size >> BDRV_SECTOR_BITS;
        ns->id = i + 1;

        if (nvme_init_namespace(n, ns, errp)) {
            return 1;
        }
    }

    return 0;
}

static void nvme_init_ctrl(FemuCtrl *n)
{
    NvmeIdCtrl *id = &n->id_ctrl;
    uint8_t *pci_conf = n->parent_obj.config;
    char *subnqn;
    int i;

    id->vid = cpu_to_le16(pci_get_word(pci_conf + PCI_VENDOR_ID));
    id->ssvid = cpu_to_le16(pci_get_word(pci_conf + PCI_SUBSYSTEM_VENDOR_ID));

    id->rab          = 6;
    id->ieee[0]      = 0x00;
    id->ieee[1]      = 0x02;
    id->ieee[2]      = 0xb3;
    id->cmic         = 0;
    id->mdts         = n->mdts;
    id->ver          = 0x00010300;
    id->oacs         = cpu_to_le16(n->oacs | NVME_OACS_DBBUF);
    id->acl          = n->acl;
    id->aerl         = n->aerl;
    id->frmw         = 7 << 1 | 1;
    id->lpa          = NVME_LPA_NS_SMART | NVME_LPA_CSE | NVME_LPA_EXTENDED;
    id->elpe         = n->elpe;
    id->npss         = 0;
    id->sqes         = (n->max_sqes << 4) | 0x6;
    id->cqes         = (n->max_cqes << 4) | 0x4;
    id->nn           = cpu_to_le32(n->num_namespaces);
    id->oncs         = cpu_to_le16(n->oncs);
    subnqn           = g_strdup_printf("nqn.2019-08.org.qemu:%s", n->serial);
    strpadcpy((char *)id->subnqn, sizeof(id->subnqn), subnqn, '\0');
    id->fuses        = cpu_to_le16(0);
    id->fna          = 0;
    id->vwc          = n->vwc;
    id->awun         = cpu_to_le16(0);
    id->awupf        = cpu_to_le16(0);
    id->psd[0].mp    = cpu_to_le16(0x9c4);
    id->psd[0].enlat = cpu_to_le32(0x10);
    id->psd[0].exlat = cpu_to_le32(0x4);

    n->wrr_enable               = true;
    n->features.arbitration     = 0x1f0f0706;
    n->features.power_mgmt      = 0;
    n->features.temp_thresh     = 0x14d;
    n->features.err_rec         = 0;
    n->features.volatile_wc     = n->vwc;
    n->features.num_io_queues   = ((n->num_io_queues - 1) | ((n->num_io_queues -
                                                              1) << 16));
    n->features.int_coalescing  = n->intc_thresh | (n->intc_time << 8);
    n->features.write_atomicity = 0;
    n->features.async_config    = 0x0;
    n->features.sw_prog_marker  = 0;

    for (i = 0; i <= n->num_io_queues; i++) {
        n->features.int_vector_config[i] = i | (n->intc << 16);
    }

    n->bar.cap = 0;
    NVME_CAP_SET_MQES(n->bar.cap, n->max_q_ents);
    NVME_CAP_SET_CQR(n->bar.cap, n->cqr);
    NVME_CAP_SET_AMS(n->bar.cap, 1);
    NVME_CAP_SET_TO(n->bar.cap, 0xf);
    NVME_CAP_SET_DSTRD(n->bar.cap, n->db_stride);
    NVME_CAP_SET_NSSRS(n->bar.cap, 0);
    NVME_CAP_SET_CSS(n->bar.cap, 1);
    NVME_CAP_SET_CSS(n->bar.cap, NVME_CAP_CSS_CSI_SUPP);
    NVME_CAP_SET_CSS(n->bar.cap, NVME_CAP_CSS_ADMIN_ONLY);

    NVME_CAP_SET_MPSMIN(n->bar.cap, n->mpsmin);
    NVME_CAP_SET_MPSMAX(n->bar.cap, n->mpsmax);

    n->bar.vs = NVME_SPEC_VER;
    n->bar.intmc = n->bar.intms = 0;
    n->temperature = NVME_TEMPERATURE;
}

static void nvme_init_cmb(FemuCtrl *n)
{
    n->bar.cmbloc = n->cmbloc;
    n->bar.cmbsz  = n->cmbsz;

    n->cmbuf = g_malloc0(NVME_CMBSZ_GETSIZE(n->bar.cmbsz));
    memory_region_init_io(&n->ctrl_mem, OBJECT(n), &nvme_cmb_ops, n, "nvme-cmb",
                          NVME_CMBSZ_GETSIZE(n->bar.cmbsz));
    pci_register_bar(&n->parent_obj, NVME_CMBLOC_BIR(n->bar.cmbloc),
                     PCI_BASE_ADDRESS_SPACE_MEMORY |
                     PCI_BASE_ADDRESS_MEM_TYPE_64, &n->ctrl_mem); }

static void nvme_init_pci(FemuCtrl *n)
{
    uint8_t *pci_conf = n->parent_obj.config;
    #ifdef INHOINNO_VERBOSE_SETTING
    femu_err("femu.c : nvme_init_pci(), to inhoinno \n");
    #endif
#if PCIe_TIME_SIMULATION
    n->pci_simulation =g_malloc0(sizeof(PCIe_Gen3_x4));
    n->pci_simulation->stime=0;
    n->pci_simulation->ntime=0;
    n->pci_simulation->bw=Interface_PCIeGen3x4_bw;
    int ret =pthread_spin_init(&n->pci_lock, PTHREAD_PROCESS_SHARED);
    if(ret)
        femu_err("femu.c:477 nvme_init_pci(): lock alloc failed, to inhoinno \n");
#endif
    pci_conf[PCI_INTERRUPT_PIN] = 1;
    /* Coperd: QEMU-OCSSD(0x1d1d,0x1f1f), QEMU-NVMe(0x8086,0x5845) */
    pci_config_set_prog_interface(pci_conf, 0x2);
    pci_config_set_vendor_id(pci_conf, n->vid);
    pci_config_set_device_id(pci_conf, n->did);
    pci_config_set_class(pci_conf, PCI_CLASS_STORAGE_EXPRESS);
    pcie_endpoint_cap_init(&n->parent_obj, 0x80);

    memory_region_init_io(&n->iomem, OBJECT(n), &nvme_mmio_ops, n, "nvme",
                          n->reg_size);
    pci_register_bar(&n->parent_obj, 0, PCI_BASE_ADDRESS_SPACE_MEMORY |
                     PCI_BASE_ADDRESS_MEM_TYPE_64, &n->iomem);
    if (msix_init_exclusive_bar(&n->parent_obj, n->num_io_queues + 1, 4, NULL)) {
        return;
    }
    msi_init(&n->parent_obj, 0x50, 32, true, false, NULL);

    if (n->cmbsz) {
        nvme_init_cmb(n);
    }
}

static int nvme_register_extensions(FemuCtrl *n)
{
    #ifdef INHOINNO_VERBOSE_SETTING
    femu_err("femu.c : nvme_register_extensions(), to inhoinno \n");
    #endif
    if (OCSSD(n)) {
        switch (n->lver) {
        case OCSSD12:
            nvme_register_ocssd12(n);
            break;
        case OCSSD20:
            nvme_register_ocssd20(n);
            break;
        default:
            break;
        }
    } else if (NOSSD(n)) {
        nvme_register_nossd(n);
    } else if (BBSSD(n)) {
        nvme_register_bbssd(n);
    } else if (ZNSSD(n)) {
        nvme_register_znssd(n);
    } else {
    }

    return 0;
}
/*
static uint16_t _nvme_init_sched_queue(NvmeSQueue * sq, FemuCtrl *n, 
                    //uint64_t dma_addr, 
                    uint16_t sqid, 
                    //uint16_t cqid, 
                    uint16_t size, 
                    enum NvmeQueueFlags prio//, int contig
                    )
{
    sq = g_malloc0(sizeof(*sq));
    sq->ctrl = n;
    sq->sqid = sqid;
    sq->size = size;
    //sq->cqid = cqid;
    sq->head = sq->tail = 0;
    sq->io_req = g_malloc0(sq->size * sizeof(*sq->io_req));
    QTAILQ_INIT(&sq->req_list);
    QTAILQ_INIT(&sq->out_req_list);
    for (int i = 0; i < sq->size; i++) {
        sq->io_req[i].sq = sq;
        QTAILQ_INSERT_TAIL(&(sq->req_list), &sq->io_req[i], entry);
    }

    switch (prio) {
    case NVME_Q_PRIO_URGENT:
        sq->arb_burst = (1 << NVME_ARB_AB(n->features.arbitration));
        break;
    case NVME_Q_PRIO_HIGH:
        sq->arb_burst = NVME_ARB_HPW(n->features.arbitration) + 1;
        break;
    case NVME_Q_PRIO_NORMAL:
        sq->arb_burst = NVME_ARB_MPW(n->features.arbitration) + 1;
        break;
    case NVME_Q_PRIO_LOW:
    default:
        sq->arb_burst = NVME_ARB_LPW(n->features.arbitration) + 1;
        break;
    }

    QTAILQ_INIT(&sq->req_list);
    QTAILQ_INIT(&sq->out_req_list);
    return 0;
}

static void nvme_init_sched_queue(FemuCtrl *n )
{
    NvmeSQueue *sq;
    uint32_t num_of_priority = 4;
    uint32_t weight_per_pqueue = 1;


    n->psched_q = g_malloc0(sizeof(*n->psched_q) * (num_of_priority*weight_per_pqueue)); //High , Med , Low 
    
    for (uint32_t i = 0; i < num_of_priority*weight_per_pqueue; i++){
        sq = g_malloc0(sizeof(*sq));
        // 0 1 2 : 0 Urgent = i/weight_per_pqueue
        // 0 1 2 : 0 1 2 order = i % weight_per_pqueue
        if((_nvme_init_sched_queue(sq, n, i, UINT16_MAX, i/weight_per_pqueue) == 0)){
            n->psched_q[i] = sq; 
            femu_log("NVMe Priority Queue [idx]:%u [Prio]:%u [#th order in same prio]:%u created",i,i/weight_per_pqueue, i%weight_per_pqueue);
        }else{
            g_free(sq);
            femu_err("Inhoinno Err femu.c:557 nvme_init_sched_queue\n");
        }
    }

}*/
static void femu_realize(PCIDevice *pci_dev, Error **errp)
{
    FemuCtrl *n = FEMU(pci_dev);
    int64_t bs_size;
    #ifdef INHOINNO_VERBOSE_SETTING
    femu_err("femu.c : femu_realize(), to inhoinno \n");
    #endif
    nvme_check_size();

    if (nvme_check_constraints(n)) {
        return;
    }

    bs_size = ((int64_t)n->memsz) * 1024 * 1024;

    init_dram_backend(&n->mbe, bs_size);
    n->mbe->femu_mode = n->femu_mode;

    n->completed = 0;
    n->start_time = time(NULL);
    n->reg_size = pow2ceil(0x1004 + 2 * (n->num_io_queues + 1) * 4);
    n->ns_size = bs_size / (uint64_t)n->num_namespaces;

    /* Coperd: [1..num_io_queues] are used as IO queues */
    //inhoinno : watchpoint
    n->sq = g_malloc0(sizeof(*n->sq) * (n->num_io_queues + 1));
    n->cq = g_malloc0(sizeof(*n->cq) * (n->num_io_queues + 1));
    n->namespaces = g_malloc0(sizeof(*n->namespaces) * n->num_namespaces);
    n->elpes = g_malloc0(sizeof(*n->elpes) * (n->elpe + 1));
    n->aer_reqs = g_malloc0(sizeof(*n->aer_reqs) * (n->aerl + 1));
    n->features.int_vector_config = g_malloc0(sizeof(*n->features.int_vector_config) * (n->num_io_queues + 1));

    nvme_init_pci(n);
    nvme_init_ctrl(n);
    nvme_init_namespaces(n, errp);

    nvme_register_extensions(n);

    if (n->ext_ops.init) {
        n->ext_ops.init(n, errp);
    }
}

static void nvme_destroy_poller(FemuCtrl *n)
{
    femu_debug("Destroying NVMe poller !!\n");

    for (int i = 1; i <= n->num_poller; i++) {
        qemu_thread_join(&n->poller[i]);
    }

    for (int i = 1; i <= n->num_poller; i++) {
        pqueue_free(n->pq[i]);
        femu_ring_free(n->to_poller[i]);
        femu_ring_free(n->to_ftl[i]);
    }

    g_free(n->should_isr);
}

static void femu_exit(PCIDevice *pci_dev)
{
    FemuCtrl *n = FEMU(pci_dev);

    femu_debug("femu_exit starting!\n");

    if (n->ext_ops.exit) {
        n->ext_ops.exit(n);
    }

    nvme_clear_ctrl(n, true);
    nvme_destroy_poller(n);
    free_dram_backend(n->mbe);

    g_free(n->namespaces);
    g_free(n->features.int_vector_config);
    g_free(n->aer_reqs);
    g_free(n->elpes);
    g_free(n->cq);
    g_free(n->sq);
    msix_uninit_exclusive_bar(pci_dev);
    memory_region_unref(&n->iomem);
    if (n->cmbsz) {
        memory_region_unref(&n->ctrl_mem);
    }
}

static Property femu_props[] = {
    DEFINE_PROP_STRING("serial", FemuCtrl, serial),
    DEFINE_PROP_UINT32("devsz_mb", FemuCtrl, memsz, 4096), /* in MB */
    DEFINE_PROP_UINT32("namespaces", FemuCtrl, num_namespaces, 1),
    DEFINE_PROP_UINT32("queues", FemuCtrl, num_io_queues, 16),
    DEFINE_PROP_UINT32("entries", FemuCtrl, max_q_ents, 0x7ff),
    DEFINE_PROP_UINT8("multipoller_enabled", FemuCtrl, multipoller_enabled, 0),
    DEFINE_PROP_UINT8("max_cqes", FemuCtrl, max_cqes, 0x4),
    DEFINE_PROP_UINT8("max_sqes", FemuCtrl, max_sqes, 0x6),
    DEFINE_PROP_UINT8("stride", FemuCtrl, db_stride, 0),
    DEFINE_PROP_UINT8("aerl", FemuCtrl, aerl, 3),
    DEFINE_PROP_UINT8("acl", FemuCtrl, acl, 3),
    DEFINE_PROP_UINT8("elpe", FemuCtrl, elpe, 3),
    DEFINE_PROP_UINT8("mdts", FemuCtrl, mdts, 10),
    DEFINE_PROP_UINT8("cqr", FemuCtrl, cqr, 1),
    DEFINE_PROP_UINT8("vwc", FemuCtrl, vwc, 0),
    DEFINE_PROP_UINT8("intc", FemuCtrl, intc, 0),
    DEFINE_PROP_UINT8("intc_thresh", FemuCtrl, intc_thresh, 0),
    DEFINE_PROP_UINT8("intc_time", FemuCtrl, intc_time, 0),
    DEFINE_PROP_UINT8("ms", FemuCtrl, ms, 16),
    DEFINE_PROP_UINT8("ms_max", FemuCtrl, ms_max, 64),
    DEFINE_PROP_UINT8("dlfeat", FemuCtrl, dlfeat, 1),
    DEFINE_PROP_UINT8("mpsmin", FemuCtrl, mpsmin, 0),
    DEFINE_PROP_UINT8("mpsmax", FemuCtrl, mpsmax, 0),
    DEFINE_PROP_UINT8("nlbaf", FemuCtrl, nlbaf, 5),
    DEFINE_PROP_UINT8("lba_index", FemuCtrl, lba_index, 0),
    DEFINE_PROP_UINT8("extended", FemuCtrl, extended, 0),
    DEFINE_PROP_UINT8("dpc", FemuCtrl, dpc, 0),
    DEFINE_PROP_UINT8("dps", FemuCtrl, dps, 0),
    DEFINE_PROP_UINT8("mc", FemuCtrl, mc, 0),
    DEFINE_PROP_UINT8("meta", FemuCtrl, meta, 0),
    DEFINE_PROP_UINT32("cmbsz", FemuCtrl, cmbsz, 0),
    DEFINE_PROP_UINT32("cmbloc", FemuCtrl, cmbloc, 0),
    DEFINE_PROP_UINT16("oacs", FemuCtrl, oacs, NVME_OACS_FORMAT),
    DEFINE_PROP_UINT16("oncs", FemuCtrl, oncs, NVME_ONCS_DSM),
    DEFINE_PROP_UINT16("vid", FemuCtrl, vid, 0x1d1d),
    DEFINE_PROP_UINT16("did", FemuCtrl, did, 0x1f1f),
    DEFINE_PROP_UINT8("femu_mode", FemuCtrl, femu_mode, FEMU_NOSSD_MODE),
    DEFINE_PROP_UINT8("flash_type", FemuCtrl, flash_type, MLC),
    DEFINE_PROP_UINT8("lver", FemuCtrl, lver, 0x2),
    DEFINE_PROP_UINT16("lsec_size", FemuCtrl, oc_params.sec_size, 4096),
    DEFINE_PROP_UINT8("lsecs_per_pg", FemuCtrl, oc_params.secs_per_pg, 4),
    DEFINE_PROP_UINT16("lpgs_per_blk", FemuCtrl, oc_params.pgs_per_blk, 512),
    DEFINE_PROP_UINT8("lmax_sec_per_rq", FemuCtrl, oc_params.max_sec_per_rq, 64),
    DEFINE_PROP_UINT8("lnum_ch", FemuCtrl, oc_params.num_ch, 2),
    DEFINE_PROP_UINT8("lnum_lun", FemuCtrl, oc_params.num_lun, 8),
    DEFINE_PROP_UINT8("lnum_pln", FemuCtrl, oc_params.num_pln, 2),
    DEFINE_PROP_UINT16("lmetasize", FemuCtrl, oc_params.sos, 16),
    // ZNS lat
    DEFINE_PROP_UINT64("zns_page_read_latency", FemuCtrl, zns_params.pg_rd_lat, 65000),
    DEFINE_PROP_UINT64("zns_page_write_latency", FemuCtrl, zns_params.pg_wr_lat, 450000),
    DEFINE_PROP_UINT64("zns_block_erasure_latency", FemuCtrl, zns_params.blk_er_lat, 3000000),
    DEFINE_PROP_UINT64("zns_channel_transfer_latency", FemuCtrl, zns_params.ch_xfer_lat, 25000),
    // ZNS Geo
    DEFINE_PROP_UINT64("zns_block_size_pages", FemuCtrl, zns_params.block_size, 4),
    DEFINE_PROP_UINT64("zns_zonesize", FemuCtrl, zns_params.zone_size, (4 * MiB)),
    DEFINE_PROP_UINT64("zns_zonecap", FemuCtrl, zns_params.zone_cap_param, 0),
    DEFINE_PROP_UINT64("zns_channels", FemuCtrl, zns_params.nchnls, 4),
    DEFINE_PROP_UINT64("zns_channels_per_zone", FemuCtrl, zns_params.chnls_per_zone, 4),
    DEFINE_PROP_UINT64("zns_ways", FemuCtrl, zns_params.ways, 2),
    DEFINE_PROP_UINT64("zns_ways_per_zone", FemuCtrl, zns_params.ways_per_zone, 2),
    DEFINE_PROP_UINT64("zns_dies_per_chip", FemuCtrl, zns_params.dies_per_chip, 1),
    DEFINE_PROP_UINT64("zns_planes_per_die", FemuCtrl, zns_params.planes_per_die, 4),
    DEFINE_PROP_UINT64("zns_zasl", FemuCtrl, zns_params.zasl, (128ULL * KiB)),
    // ZNS modes
    DEFINE_PROP_UINT8("zns_allow_partial_resets", FemuCtrl, zns_params.allow_partial_zone_resets, 1),
    DEFINE_PROP_UINT8("zns_asynchronous_resets", FemuCtrl, zns_params.asynchronous_resets, 1),
    // ZNS VTable mode (0 == direct, 1 == lazy)
    DEFINE_PROP_UINT8("zns_vtable_mode", FemuCtrl, zns_params.vtable_mode, 0),
    // End
    DEFINE_PROP_END_OF_LIST(),
};

static const VMStateDescription femu_vmstate = {
    .name = "femu",
    .unmigratable = 1,
};

static void femu_class_init(ObjectClass *oc, void *data)
{
    DeviceClass *dc = DEVICE_CLASS(oc);
    PCIDeviceClass *pc = PCI_DEVICE_CLASS(oc);
    #ifdef INHOINNO_VERBOSE_SETTING
    femu_err("femu.c : femu_class_init(), to inhoinno \n");
    #endif
    pc->realize = femu_realize;
    pc->exit = femu_exit;
    pc->class_id = PCI_CLASS_STORAGE_EXPRESS;
    pc->vendor_id = PCI_VENDOR_ID_INTEL;
    pc->device_id = 0x5845;
    pc->revision = 2;

    set_bit(DEVICE_CATEGORY_STORAGE, dc->categories);
    dc->desc = "FEMU Non-Volatile Memory Express";
    device_class_set_props(dc, femu_props);
    dc->vmsd = &femu_vmstate;
}

static const TypeInfo femu_info = {
    .name          = "femu",
    .parent        = TYPE_PCI_DEVICE,
    .instance_size = sizeof(FemuCtrl),
    .class_init    = femu_class_init,
    .interfaces = (InterfaceInfo[]) {
        { INTERFACE_PCIE_DEVICE },
        { }
    },
};

static void femu_register_types(void)
{
    type_register_static(&femu_info);
}

type_init(femu_register_types)
