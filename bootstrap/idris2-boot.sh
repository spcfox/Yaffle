#!/bin/sh

set -e # exit on any error

if [ -z "$SCHEME" ]; then
    echo "Required SCHEME env is not set."
    exit 1
fi

if [ "$OS" = windows ] || [ "$OS" = Windows_NT ]; then
    DIR=$(dirname "$(readlink -f -- "$0" || cygpath -a -- "$0")")
    PATH=$DIR/yaffle_app:$PATH
elif [ "$(uname)" = Darwin ]; then
    DIR=$(zsh -c 'printf %s "$0:A:h"' "$0")
else
    DIR=$(dirname "$(readlink -f -- "$0")")
fi

export LD_LIBRARY_PATH="$DIR/yaffle_app:$LD_LIBRARY_PATH"
export DYLD_LIBRARY_PATH="$DIR/yaffle_app:$DYLD_LIBRARY_PATH"

${SCHEME} --script "$DIR/yaffle_app/yaffle-boot.so" "$@"
