#!/usr/bin/env bash
set -euo pipefail
if git grep -nE '(^|[^[:alnum:]_])(sorry|admit)([^[:alnum:]_]|$)|^[[:space:]]*(axiom|constant)[[:space:]]' -- '*.lean'; then
  echo "Unproved declarations or proof placeholders found." >&2
  exit 1
fi
lake build
lake env lean Audit.lean
