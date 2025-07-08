#!/bin/bash
#
# Huaicheng Li <hcli@cmu.edu>
# Run FEMU as Zoned-Namespace (ZNS) SSDs
#

# Image directory
OSIMGF=/home/teona/femu.qcow2

if [[ ! -e "$OSIMGF" ]]; then
	echo ""
	echo "VM disk image couldn't be found ..."
	echo "Please prepare a usable VM image and place it as $OSIMGF"
	echo "Once VM disk image is ready, please rerun this script again"
	echo ""
	exit
fi

sudo x86_64-softmmu/qemu-system-x86_64 \
    -name "FEMU-ZNSSD" \
    -enable-kvm \
    -cpu host \
    -smp 20 \
    -m 64G \
    -device virtio-scsi-pci,id=scsi0 \
    -device scsi-hd,drive=hd0 \
    -drive file=$OSIMGF,if=none,aio=native,cache=none,format=qcow2,id=hd0 \
    -device femu,devsz_mb=$((8)),id=nvme0,femu_mode=3,queues=64,zns_zonesize=4194304,zns_zonecap=$((4194304)),zns_channels=4,zns_channels_per_zone=4,zns_ways=2,zns_ways_per_zone=2,zns_dies_per_chip=1,zns_planes_per_die=4,zns_page_write_latency=$((700000)),zns_page_read_latency=60000,zns_channel_transfer_latency=25000,zns_block_erasure_latency=3500000,zns_allow_partial_resets=1,zns_vtable_mode=4,zns_block_size_pages=4\
    -net user,hostfwd=tcp::8080-:22 \
    -net nic,model=virtio \
    -nographic \
    -qmp unix:./qmp-sock,server,nowait 2>&1 | tee log

