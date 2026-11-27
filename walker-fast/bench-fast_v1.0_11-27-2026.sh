#!/bin/zsh
# old (wall-walk-thirty) against new (wall-walk-fast), both on 8 threads, back to back; load noted before each run
cd "$(dirname "$0")"
LOG=bench-fast_v1.0_11-27-2026.txt
{
echo "build: clang -O3 -mcpu=native -o wall-walk-fast wall-walk-fast_v1.0_11-27-2026.c -lpthread"
echo "build: clang -O3 -mcpu=native -o wall-walk-thirty-old ../fable-improvements_v1.0_11-27-2026/wall-walk-thirty_v1.0_11-27-2026.c -lpthread"
echo "machine: $(sysctl -n machdep.cpu.brand_string), $(sysctl -n hw.ncpu) cores, shared with other jobs"
} > $LOG
for N in 1e11 1e12; do
  echo "=== old wall-walk-thirty $N 8 ===" >> $LOG; uptime >> $LOG; ./wall-walk-thirty-old $N 8 >> $LOG 2>&1
  echo "=== new wall-walk-fast $N 8 ===" >> $LOG; uptime >> $LOG; ./wall-walk-fast $N 8 >> $LOG 2>&1
done
echo "=== bench pair done ===" >> $LOG
