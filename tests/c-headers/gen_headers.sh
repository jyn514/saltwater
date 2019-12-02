#!/usr/bin/env bash

HEADERS=(
	assert
	complex
	ctype
	errno
	fenv
	float
	inttypes
	limits
	locale
	math
	setjmp
	signal
	stdalign
	stdarg
	stdatomic
	stdbool
	stddef
	stdint
	stdio
	stdlib
	stdnoreturn
	string
	time
	uchar
	wchar
	wctype
)

for header in "${HEADERS[@]}"; do
	cpp -P -undef <<< "#include <$header.h>" > $header.c
	if ! [ -s $header.c ]; then rm $header.c; fi
done
