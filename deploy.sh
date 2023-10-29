#!/usr/bin/env bash
set -e

[ -z "$LEAN_REMOTE_TP_LEAN" ] && echo "LEAN_REMOTE_TP_LEAN is not set" && exit 1

# clean up
rm -rf build
mdbook build
cd build
git init
git add -A
git commit -m "Update `date`"
git push $LEAN_REMOTE_TP_LEAN +HEAD:gh-pages
