#!/usr/bin/env bash
# attempt.sh <statement-id> <proof-script-file> <agent-name> [--tokens N] [--time-limit SECONDS]
# One attempt at one statement, judged by the HOL4 kernel. See attempt.py for what is checked.
exec python3 "$(cd "$(dirname "$0")" && pwd)/attempt.py" "$@"
