### How to use:

- `input` = relative/absolute path to input file
- `script` = script name in `conditions` subfolder
- `args` = arguments to above script

`.minimize.sh <input> "<script>  <args>"`

It is important to put the condition script and its arguments
in quotes so they end up as one argument inside of `minimize.sh`.

### Examples:
`./path/to/minimize.sh ~/Downloads/panicking-input.c "return_code_equals.sh 101"`

This will produce a new file named `panicking-input-reduced.c`
next to `minimize.sh` if execution and reduction was successful.
