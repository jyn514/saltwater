### How to use:

- `input` = relative/absolute path to input file
- `script` = script name in `conditions` subfolder
- `args` = arguments to above script

`./minimize.sh <input> <script> <args>`

### Examples:
`./path/to/minimize.sh panicking-input.c return_code_equals 101`
`./path/to/minimize.sh unreachable-panic.c output_contains unreachable`

This will produce new files named `panicking-input-reduced.c`
and `unreachable-panic-reduced.c` next to `minimize.sh`
if execution and reduction was successful.
