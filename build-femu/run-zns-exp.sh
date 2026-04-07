#!/bin/bash
set -e

# Image directory
OSIMGF=/path/to/femu.qcow2

if [ $# -ne 20 ]; then
    echo "Usage: $0 <zns_vtable_mode> <zns_chunk_size> <zns_max_chunks_per_lun> <zns_min_luns> <zns_log_path> <zns_log_path_time> <zns_zonesize> <zns_zonecap> <zns_channels_per_zone> <zns_ways_per_zone> <zns_channels> <zns_ways> <zns_dies_per_chip> <zns_planes_per_die> <zns_block_size_pages> <zns_page_write_latency> <zns_page_read_latency> <zns_channel_transfer_latency> <zns_block_erasure_latency> <devsz_mb>"
    echo
    echo "Example:"
    echo "  $0 2 1 1 16 /tmp/finish-log /tmp/allocation-log 134217728 134217728 8 2 8 2 1 1 2048 500000 50000 25000 5000000 16384"
    echo
    echo "Arguments:"
    echo "  1  zns_vtable_mode"
    echo "  2  zns_chunk_size"
    echo "  3  zns_max_chunks_per_lun"
    echo "  4  zns_min_luns"
    echo "  5  zns_log_path"
    echo "  6  zns_log_path_time"
    echo "  7  zns_zonesize"
    echo "  8  zns_zonecap"
    echo "  9  zns_channels_per_zone"
    echo "  10 zns_ways_per_zone"
    echo "  11 zns_channels"
    echo "  12 zns_ways"
    echo "  13 zns_dies_per_chip"
    echo "  14 zns_planes_per_die"
    echo "  15 zns_block_size_pages"
    echo "  16 zns_page_write_latency"
    echo "  17 zns_page_read_latency"
    echo "  18 zns_channel_transfer_latency"
    echo "  19 zns_block_erasure_latency"
    echo "  20 devsz_mb"
    exit 1
fi

zns_vtable_mode="$1"              # 0: direct, 1: lazy, 2: full, 3: flexible, 4: stripe
zns_chunk_size="$2"
zns_max_chunks_per_lun="$3"
zns_min_luns="$4"
zns_log_path="$5"
zns_log_path_time="$6"
zns_zonesize="$7"
zns_zonecap="$8"
zns_channels_per_zone="$9"
zns_ways_per_zone="${10}"

# SSD Geometry
zns_channels="${11}"
zns_ways="${12}"
zns_dies_per_chip="${13}"
zns_planes_per_die="${14}"
zns_block_size_pages="${15}"

# SSD Timing
zns_page_write_latency="${16}"
zns_page_read_latency="${17}"
zns_channel_transfer_latency="${18}"
zns_block_erasure_latency="${19}"

# Device size
devsz_mb="${20}"

if [[ ! -e "$OSIMGF" ]]; then
    echo ""
    echo "VM disk image couldn't be found ..."
    echo "Please prepare a usable VM image and place it as $OSIMGF"
    echo "Once VM disk image is ready, please rerun this script again"
    echo ""
    exit 1
fi

femu_mode=3   # use 3 for ZNS mode
queues=64

# ZNS specific config
zns_allow_partial_resets=1
zns_asynchronous_resets=1
zns_debug=1

echo "Launching FEMU with:"
echo "  zns_vtable_mode=${zns_vtable_mode}"
echo "  zns_chunk_size=${zns_chunk_size}"
echo "  zns_max_chunks_per_lun=${zns_max_chunks_per_lun}"
echo "  zns_min_luns=${zns_min_luns}"
echo "  zns_log_path=${zns_log_path}"
echo "  zns_log_path_time=${zns_log_path_time}"
echo "  zns_zonesize=${zns_zonesize}"
echo "  zns_zonecap=${zns_zonecap}"
echo "  zns_channels_per_zone=${zns_channels_per_zone}"
echo "  zns_ways_per_zone=${zns_ways_per_zone}"
echo "  zns_channels=${zns_channels}"
echo "  zns_ways=${zns_ways}"
echo "  zns_dies_per_chip=${zns_dies_per_chip}"
echo "  zns_planes_per_die=${zns_planes_per_die}"
echo "  zns_block_size_pages=${zns_block_size_pages}"
echo "  zns_page_write_latency=${zns_page_write_latency}"
echo "  zns_page_read_latency=${zns_page_read_latency}"
echo "  zns_channel_transfer_latency=${zns_channel_transfer_latency}"
echo "  zns_block_erasure_latency=${zns_block_erasure_latency}"
echo "  devsz_mb=${devsz_mb}"

# QEMU Launch
sudo x86_64-softmmu/qemu-system-x86_64 \
    -name "FEMU-ZNSSD" \
    -enable-kvm \
    -cpu host \
    -smp 20 \
    -m 64G \
    -device virtio-scsi-pci,id=scsi0 \
    -device scsi-hd,drive=hd0 \
    -drive file=$OSIMGF,if=none,aio=native,cache=none,format=qcow2,id=hd0 \
    -device femu,devsz_mb=${devsz_mb},id=nvme0,femu_mode=${femu_mode},queues=${queues},\
zns_zonesize=${zns_zonesize},zns_zonecap=${zns_zonecap},\
zns_channels=${zns_channels},zns_channels_per_zone=${zns_channels_per_zone},\
zns_ways=${zns_ways},zns_ways_per_zone=${zns_ways_per_zone},\
zns_dies_per_chip=${zns_dies_per_chip},zns_planes_per_die=${zns_planes_per_die},\
zns_page_write_latency=${zns_page_write_latency},zns_page_read_latency=${zns_page_read_latency},\
zns_channel_transfer_latency=${zns_channel_transfer_latency},zns_block_erasure_latency=${zns_block_erasure_latency},\
zns_allow_partial_resets=${zns_allow_partial_resets},zns_asynchronous_resets=${zns_asynchronous_resets},\
zns_vtable_mode=${zns_vtable_mode},zns_block_size_pages=${zns_block_size_pages},\
zns_chunk_size=${zns_chunk_size},zns_max_chunks_per_lun=${zns_max_chunks_per_lun},zns_min_luns=${zns_min_luns},\
zns_debug=${zns_debug},zns_log_path=${zns_log_path},zns_log_path_time=${zns_log_path_time} \
    -net user,hostfwd=tcp::8080-:22 \
    -net nic,model=virtio \
    -nographic \
    -qmp unix:./qmp-sock,server,nowait 2>&1 | tee log