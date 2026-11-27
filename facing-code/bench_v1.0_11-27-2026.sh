#!/bin/zsh
# old (walls of six, wall-walk-max) against new (walls of thirty) on 12 threads; same machine, runs one after another
cd "$(dirname "$0")"
LOG=wall-walk-thirty-bench_v1.0_11-27-2026.txt
: > $LOG
for N in 1e11 1e12; do
  echo "=== old wall-walk-max walk $N 12 ===" >> $LOG; ./wall-walk-max-old walk $N 12 >> $LOG 2>&1
  echo "=== new wall-walk-thirty $N 12 ===" >> $LOG; ./wall-walk-thirty $N 12 >> $LOG 2>&1
done
echo "=== new wall-walk-thirty 1e13 12 ===" >> $LOG; ./wall-walk-thirty 1e13 12 >> $LOG 2>&1
echo "=== done ===" >> $LOG
