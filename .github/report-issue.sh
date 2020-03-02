#!/bin/sh

set -eu

if [ $# -lt 2 ]; then
	echo "usage: $0 <issue type> <file>"
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

exists() {
	command -v "$1" >/dev/null 2>&1
}
abort_unless_override() {
	read -r
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
	read -r
	echo "$REPLY"
}
editor() {
	fallback editor "$EDITOR" "$VISUAL" xdg-open open
}
browser() {
	fallback browser xdg-open sensible-browser x-www-browser firefox chromium-browser
}

# running from git
if exists git && exists cargo \
	&& git remote -v | grep -q https://github.com/jyn514/rcc; then
	BRANCH="$(git rev-parse --abbrev-ref HEAD)"
	if ! [ "$BRANCH" = master ]; then
		printf "You are on '%s', not master. Continue? y/[n] " "$BRANCH"
		abort_unless_override
	fi
	# https://stackoverflow.com/a/2659808
	if ! git diff-index --quiet HEAD --; then
		printf "You have staged or unstaged changes relative to master. Continue? y/[n]"
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
$RCC "$SOURCE" >"$T/stdout" 2>"$T/stderr"

if grep -q RUST_BACKTRACE "$TEMPLATE"; then
	RUST_BACKTRACE=1 $RCC "$SOURCE" > "$T/backtrace"
else
	touch "$T/backtrace"
fi

"$ROOT/.github/sub.py" "$T/backtrace" "$SOURCE" < "$TEMPLATE" > "$T/template-backtrace"
TEMPLATE="$T/template-backtrace"

cp "$TEMPLATE" "$T/template"
$(editor) "$T/template"
if exists xclip; then
	xclip < "$T/template"
	echo "copied to clipboard"
fi
TITLE="$(grep '^title: ' < "$T/template" | tail -c +8)"
# https://stackoverflow.com/questions/59257913/remove-header-yaml-with-sed-from-a-markdown-file
BODY="$(sed '/^---$/,/^---$/d' "$T/template")"
URL="https://github.com/jyn514/rcc/issues/new?template=$TYPE&title=$TITLE&body=$BODY"
$(browser) "$URL"
