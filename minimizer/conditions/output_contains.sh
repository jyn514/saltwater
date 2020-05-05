#!/usr/bin/env bash

cargo run -- --color never input.c 2>&1 | grep "$1"
exit $?;
 
