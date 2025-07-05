# #!/bin/bash

# NRCPUS="$(cat /proc/cpuinfo | grep "vendor_id" | wc -l)"

# make clean

# export MOSEKLM_LICENSE_FILE="/home/teona/mosek/mosek.lic"

# # --disable-werror --extra-cflags=-w --disable-git-update
# # Configure the build with additional paths for Mosek and Python
# ../configure --enable-kvm --target-list=x86_64-softmmu --disable-werror \
#     --extra-cflags="$(python3-config --includes) -Wno-format -Wno-sign-compare -Wno-unused-variable -Wno-unused-result -Wno-missing-prototypes -Wno-redundant-decls -Wno-type-limits
#     --extra-ldflags="$(python3-config --ldflags) -L/usr/local/lib/python3.10/config-3.10-x86_64-linux-gnu -L/usr/local/lib/python3.10/dist-packages -L/usr/lib/x86_64-linux-gnu -L/u

# make -j $NRCPUS

# echo ""
# echo "===> FEMU compilation done ..."
# echo ""
# exit


#!/bin/bash

NRCPUS="$(nproc)"

make clean

export MOSEKLM_LICENSE_FILE="/root/mosek/mosek.lic"

# Ensure MOSEK library path is included at runtime
export LD_LIBRARY_PATH="/home/teona/mosek/11.0/tools/platform/linux64x86/bin:$LD_LIBRARY_PATH"

# Configure the build with MOSEK paths
../configure --enable-kvm --target-list=x86_64-softmmu --disable-werror \
    --extra-cflags="-I/home/teona/mosek/11.0/tools/platform/linux64x86/h \
    -Wno-format -Wno-sign-compare -Wno-unused-variable -Wno-unused-result \
    -Wno-missing-prototypes -Wno-redundant-decls -Wno-type-limits -Wno-unused-but-set-variable \
    -Wno-maybe-uninitialized -DMOSEKLM_LICENSE_FILE='\"/root/mosek/mosek.lic\"'" \
    --extra-ldflags="-L/home/teona/mosek/11.0/tools/platform/linux64x86/bin \
    -lmosek64 -Wl,-rpath,/home/teona/mosek/11.0/tools/platform/linux64x86/bin"

# Ensure CFLAGS and LDFLAGS are set correctly
export CFLAGS="-I/home/teona/mosek/11.0/tools/platform/linux64x86/h $CFLAGS"
export LDFLAGS="-L/home/teona/mosek/11.0/tools/platform/linux64x86/bin -lmosek64 -Wl,-rpath,/home/teona/mosek/11.0/tools/platform/linux64x86/bin $LDFLAGS"

# Recompile the project
make -j "$NRCPUS"

echo ""
echo "===> FEMU compilation done ..."
echo ""

exit