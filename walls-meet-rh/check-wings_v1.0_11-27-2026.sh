#!/bin/sh
# Kernel-check WingFamiliesGRH against the built RH repo (uses its oleans; writes nothing there).
# Step 1: compile the Sharp file (module name WallsMeetRHSharp) to an olean in ./build.
# Step 2: check the wings file with that olean on the LEAN_PATH.
W="$HOME/HaveMindHive/walls-meet-rh_v1.0_11-27-2026"
B="$W/build"
cd "$HOME/Library/CloudStorage/OneDrive-rkfleming/HaveMindHive/riemann-hypothesis-community_v1.0_11-27-2026/repo" || exit 1
mkdir -p "$B"
cp "$W/WallsMeetRHSharp_v1.0_11-27-2026.lean" "$B/WallsMeetRHSharp.lean"
lake env lean --root="$B" -o "$B/WallsMeetRHSharp.olean" -i "$B/WallsMeetRHSharp.ilean" "$B/WallsMeetRHSharp.lean" > "$B/sharp-check.txt" 2>&1 || { echo "Sharp failed"; cat "$B/sharp-check.txt"; exit 1; }
LEAN_PATH="$B:$(lake env printenv LEAN_PATH)" lake env lean "$W/WingFamiliesGRH_v1.0_11-27-2026.lean"
