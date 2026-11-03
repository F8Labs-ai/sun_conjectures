#!/bin/zsh
# Kernel-checks the 103 member chunks of the 2.9 certificate, 5 at a time, then Sun29.
cd "$(dirname "$0")/../.."
N=103; B=5; start=$(date +%s)
for ((i = 0; i < N; i += B)); do
  t=()
  for ((j = i; j < i + B && j < N; ++j)); do t+=(Sunproj.Triple.Data.T$(printf %03d $j)); done
  if ! ~/.elan/bin/lake build $t > /tmp/claude_lake29_batch.log 2>&1; then
    echo "FAILED at batch $i"; grep -E "error" -A5 /tmp/claude_lake29_batch.log | head -30; exit 1
  fi
  done_=$(( i + B < N ? i + B : N )); el=$(( $(date +%s) - start ))
  printf "\r[%3d/%d chunks]  %d of 77055 triples kernel-checked  elapsed %ds  eta %ds   " \
    $done_ $N $(( done_ * 750 < 77055 ? done_ * 750 : 77055 )) $el $(( el * (N - done_) / done_ ))
done
echo; echo "ALL CHUNKS OK in $(( $(date +%s) - start ))s"
if ~/.elan/bin/lake build Sunproj.Triple.Sun29 > /tmp/claude_lake29_final.log 2>&1; then
  echo "Sun29 OK in $(( $(date +%s) - start ))s"
else
  echo "Sun29 FAILED"; grep -E "error" -A8 /tmp/claude_lake29_final.log | head -40
fi
