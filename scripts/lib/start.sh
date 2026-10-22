#!/usr/bin/env bash
# scripts/lib/start.sh — sourced by the three start-vaelii scripts, for the two things
# they share: the KB directory they open and the JVM options they add.
#
# The caller sets ROOT to the checkout before sourcing this file.

# start_kb_dir [DIR] prints the KB directory as a physical path: DIR, else `checkouts/kb`
# beside the checkout, which is gitignored and which you point at a KB yourself. It
# resolves a symlink, so the catalog names the KB after the directory the link points at.
# It prints a message and returns 1 when the path is not a directory, so a caller writes
# `KB="$(start_kb_dir "$arg")" || exit 1`.
start_kb_dir() {
  local dir="${1:-$ROOT/checkouts/kb}"
  if [ ! -d "$dir" ]; then
    echo "no KB directory at $dir — pass one, or point checkouts/kb at one" >&2
    return 1
  fi
  (cd "$dir" && pwd -P)
}

# start_profiles KB prints the Leiningen profiles KB's record store needs, comma-joined,
# or nothing. A KB whose records live on a postgres server holds `index/records.edn`
# naming that server (docs/storage.md), and opening it loads the vaelii-postgres
# adapter, which `+with-postgres` puts on the classpath with its driver. A caller
# writes `lein with-profile "+x,$(start_profiles "$KB")"` or `${p:+with-profile "$p"}`.
start_profiles() {
  if [ -f "$1/index/records.edn" ]; then echo "+with-postgres"; fi
}

# start_jvm_opts prints the JVM options every start script adds to JVM_OPTS: the heap
# ceiling VAELII_HEAP (default 40g), and an exit on OutOfMemoryError, so a process that
# ran out of heap stops instead of serving a KB it did not finish building. A recover
# short of heap spends most of its time in full collections rather than failing, and the
# exit turns that into an error.
start_jvm_opts() {
  echo "-Xmx${VAELII_HEAP:-40g} -XX:+ExitOnOutOfMemoryError"
}
