#!/bin/sh
#   The test of the hash_consing library: every
#   fixture in its own process at the day-to-day budget,
#   --stack-limit=32m --table-space=32m outside, call_with_time_limit(1)
#   around each query inside, `timeout 20` around process startup.
#
#   Usage: ./hash_consing_rewrite.sh | diff - hash_consing_rewrite_baseline.txt
#   must print nothing.
SELF_DIRECTORY="$(cd "$(dirname "$0")" && pwd)"
cd "$SELF_DIRECTORY" || exit 1
for FIXTURE in steps spines plain inner_dispatch reconfigured; do
  LANG=C.UTF-8 LC_ALL=C.UTF-8 timeout 20 \
    swipl -q --stack-limit=32m --table-space=32m hash_consing_rewrite.pl -- --fixture="$FIXTURE" 2>&1 \
    || echo "fixture($FIXTURE, process_exit($?))"
done
