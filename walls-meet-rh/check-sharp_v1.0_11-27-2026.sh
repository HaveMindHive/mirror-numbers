#!/bin/sh
# Kernel-check WallsMeetRHSharp against the built RH repo (uses its oleans; writes nothing there).
cd "$HOME/Library/CloudStorage/OneDrive-rkfleming/HaveMindHive/riemann-hypothesis-community_v1.0_11-27-2026/repo" &&
  lake env lean "$HOME/HaveMindHive/walls-meet-rh_v1.0_11-27-2026/WallsMeetRHSharp_v1.0_11-27-2026.lean"
