#!/usr/bin/env bash

if ! [[ -x "$(command -v dustmite)" ]]; then
    echo "No DustMite installed. It is typically contained in a package called 'dtools'."
    exit 1
fi

available_scripts=()
for filename in ./conditions/*.sh; do
    filename=$(basename -- "$filename")
    filename="${filename%.*}"
    available_scripts+=("$filename")
done

if [[ $# -lt 2 ]]; then
    echo "usage: $0 <file> <condition>"
    echo "available conditions are:"
    printf '\t%s\n' "${available_scripts[@]}"
    exit 1
fi

FILE="$1"

if ! test -f "$FILE"; then
    echo "Input file '$FILE' not found."
    exit 1
fi

SCRIPT_PATH=$(cd "$(dirname "${BASH_SOURCE[0]}")" || exit; pwd -P)
CONDITION_SCRIPT="$2"

if ! test -f "$SCRIPT_PATH/conditions/$CONDITION_SCRIPT.sh"; then
    echo "Condition script '$SCRIPT_PATH/conditions/$CONDITION_SCRIPT.sh' not found."
    echo "available conditions are:"
    printf '\t%s\n' "${available_scripts[@]}"
    exit 1
fi

shift
shift
CONDITION="$*"
WORKSPACE=$SCRIPT_PATH/workspace
mkdir "$WORKSPACE"
ln -s "$FILE" "$WORKSPACE"/input.c

dustmite --strip-comments --split "*.c:d" "$WORKSPACE"/input.c "$SCRIPT_PATH/conditions/$CONDITION_SCRIPT.sh $CONDITION"

if ! [[ -d "$WORKSPACE/input.reduced" ]]; then
    echo "DustMite failed. Cleaning up..."
    rm "$WORKSPACE"/input.c
    rmdir "$WORKSPACE"

    exit 1;
else
    if ! [[ -f "$WORKSPACE/input.reduced/input.c" ]]; then
        echo "DustMite failed. Cleaning up..."
        rm -r "$WORKSPACE"
        exit 1
    else
        rm "$WORKSPACE"/input.c

        filename=$(basename -- "$FILE")
        extension="${filename##*.}"
        filename="${filename%.*}"
        filename="$SCRIPT_PATH/$filename-reduced.$extension"

        mv "$WORKSPACE"/input.reduced/input.c "$filename"
        echo "Ignore the above. The file is actually here: $filename"
        rm -r "$WORKSPACE"
    fi
fi
