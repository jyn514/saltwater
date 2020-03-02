#!/bin/sh

set -eu

if [ $# -lt 2 ]; then
	echo "usage: $0 <issue type> <file> [-f]"
	exit 1
fi

case "$1" in
	ice|crash|fuzz|panic) TYPE=panic;;
	ir|codegen*) TYPE=codegen_bug;;
	parse*|bad*) TYPE=bad_parse;;
	*) echo "unrecognized issue type (options are panic, codegen, parse), aborting"
	   exit 1;;
esac

ROOT="$(git rev-parse --show-toplevel)"
TEMPLATE="$ROOT/.github/ISSUE_TEMPLATE/$TYPE.md"
SOURCE="$2"
if [ $# = 3 ] && [ "$3" = "-f" ]; then
	FORCE=1
else
	echo $#
	FORCE=0
fi

if ! [ -e "$TEMPLATE" ]; then
	echo "INTERNAL error: template $TEMPLATE does not exist"
	exit 3
fi

if ! [ -f "$SOURCE" ]; then
	echo "error: C source code file $SOURCE does not exist or is not a file"
	exit 4
fi

exists() {
	command -v "$1" >/dev/null 2>&1
}
abort_unless_override() {
	read -r REPLY
	if ! [ "$REPLY" = y ]; then
		echo "aborting"
		exit 1
	fi
}
fallback() {
	prompt="$1"
	shift
	while [ $# -gt 0 ]; do
		if exists "$1"; then
			echo "$1"
			return
		fi
		shift
	done
	echo "What is your preferred $prompt? (ctrl+c to exit): " >/dev/tty
	read -r REPLY
	echo "$REPLY"
}
editor() {
	EDITOR=${EDITOR:-${VISUAL:-xdg-open}}
	fallback editor "$EDITOR" open
}
browser() {
	BROWSER=${BROWSER:-xdg-open}
	fallback browser "$BROWSER" sensible-browser x-www-browser firefox chromium-browser
}

# running from git
# NOTE: allows ssh urls too
if exists git && exists cargo && git remote -v | grep -q 'github\.com.jyn514/rcc'; then
	BRANCH="$(git rev-parse --abbrev-ref HEAD)"
	if [ $FORCE = 0 ] && ! [ "$BRANCH" = master ]; then
		printf "You are on '%s', not master. Continue? y/[n] " "$BRANCH"
		abort_unless_override
	fi
	# https://stackoverflow.com/a/2659808
	if [ $FORCE = 0 ] && ! git diff-index --quiet HEAD --; then
		printf "You have staged or unstaged changes relative to master. Continue? y/[n] "
		abort_unless_override
	fi
	cargo build
	RCC="cargo run --quiet"
# installed globally
elif exists rcc; then
	RCC=rcc
else
	echo "'rcc' not found in PATH and not in the rcc git directory."
	echo "Try changing to the 'rcc' git directory."
	exit 2
fi

T="$(mktemp -d /tmp/rcc-XXXXXX)"
$RCC "$SOURCE" >"$T/stdout" 2>"$T/stderr" || true

if grep -q RUST_BACKTRACE "$TEMPLATE"; then
	RUST_BACKTRACE=pretty $RCC "$SOURCE" 2> "$T/backtrace" || true
else
	touch "$T/backtrace"
fi

cat "$SOURCE" "$T/stdout" "$T/stderr" > "$T/combined"
python3 -c '
import sys

with open(sys.argv[1]) as fd:
    backtrace = fd.read()
with open(sys.argv[2]) as fd:
    source = fd.read()

for line in sys.stdin:
    print(line, end="")
    if "RUST_BACKTRACE=1" in line:
        line = input()
        while line == "":
            print()
            line = input()
        print(line)
        if "```" not in line:
            continue
        print(backtrace, end="")
    # source code for file
    elif "```c" in line:
        print(source, end="")
' "$T/backtrace" "$T/combined" < "$TEMPLATE" > "$T/template"
$(editor) "$T/template"
if exists xclip; then
	xclip < "$T/template"
	echo "copied to clipboard"
fi

TITLE="$(grep '^title: ' < "$T/template" | tail -c +8 | tr -d '"')"
LABELS="$(grep '^labels: ' < "$T/template" | tail -c +9 | tr -d '"')"
# https://stackoverflow.com/questions/59257913/remove-header-yaml-with-sed-from-a-markdown-file
BODY="$(sed '/^---$/,/^---$/d' "$T/template" | python3 -c "import urllib.parse; import sys; print(urllib.parse.quote(sys.stdin.read()))")"
URL="https://github.com/jyn514/rcc/issues/new?template=$TYPE.md&title=$TITLE&labels=$LABELS&body=$BODY"
$(browser) "$URL"
rm -rf "$T"
