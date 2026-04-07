#!/bin/bash

NRCPUS="$(nproc)"

make clean

# === Configure MOSEK paths ===
# Update these paths based on your installation

export MOSEK_ROOT="/path/to/mosek"
export MOSEK_PLATFORM="$MOSEK_ROOT/11.0/tools/platform/linux64x86"

export MOSEKLM_LICENSE_FILE="/path/to/mosek/license/mosek.lic"

# Ensure MOSEK library path is included at runtime
export LD_LIBRARY_PATH="$MOSEK_PLATFORM/bin:$LD_LIBRARY_PATH"

# Configure the build with MOSEK paths
../configure --enable-kvm --target-list=x86_64-softmmu --disable-werror \
    --extra-cflags="-I$MOSEK_PLATFORM/h \
    -Wno-format -Wno-sign-compare -Wno-unused-variable -Wno-unused-result \
    -Wno-missing-prototypes -Wno-redundant-decls -Wno-type-limits -Wno-unused-but-set-variable \
    -Wno-maybe-uninitialized -DMOSEKLM_LICENSE_FILE='\"$MOSEKLM_LICENSE_FILE\"'" \
    --extra-ldflags="-L$MOSEK_PLATFORM/bin \
    -lmosek64 -Wl,-rpath,$MOSEK_PLATFORM/bin"

# Ensure CFLAGS and LDFLAGS are set correctly
export CFLAGS="-I$MOSEK_PLATFORM/h $CFLAGS"
export LDFLAGS="-L$MOSEK_PLATFORM/bin -lmosek64 -Wl,-rpath,$MOSEK_PLATFORM/bin $LDFLAGS"

# Recompile the project
make -j "$NRCPUS"

echo ""
echo "===> FEMU compilation done ..."
echo ""

exit