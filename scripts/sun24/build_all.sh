#!/bin/zsh
# Kernel-checks all certificate chunks, 5 at a time, with a progress line.
cd "$(dirname "$0")/../.."
N=378; B=5; start=$(date +%s)
for ((i = 0; i < N; i += B)); do
  t=()
  for ((j = i; j < i + B && j < N; ++j)); do t+=(Sunproj.PrimRoot.Data.C$(printf %03d $j)); done
  if ! ~/.elan/bin/lake build $t > /tmp/claude_lake_batch.log 2>&1; then
    echo "FAILED at batch $i"; grep -E "error" /tmp/claude_lake_batch.log | head; exit 1
  fi
  done_=$(( i + B < N ? i + B : N )); el=$(( $(date +%s) - start ))
  printf "\r[%3d/%d chunks]  %d of 754589 members kernel-checked  elapsed %ds  eta %ds   " \
    $done_ $N $(( done_ * 2000 < 754589 ? done_ * 2000 : 754589 )) $el $(( el * (N - done_) / done_ ))
done
echo; echo "ALL CHUNKS OK in $(( $(date +%s) - start ))s"
