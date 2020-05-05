#!/usr/bin/env bash

cargo run -- --color never input.c 2>&1;
if [[ $? != $1 ]]; then exit 0; fi
exit 1;
