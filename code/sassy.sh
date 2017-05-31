#!/bin/bash

ANALYSIS_DIR=$1
ANALYSIS_NAME=${ANALYSIS_DIR%-*}

SASSY_CMD=`./Imp.native --generate-constraints Imp/sassy-analyses/$ANALYSIS_DIR --lattice $ANALYSIS_NAME | python sassy-post-process.py`

# remove emacs backups in test dir because they are annoying
rm Imp/sassy-analyses/$ANALYSIS_DIR/*~ &> /dev/null

echo "$SASSY_CMD"; echo "-----------------------"

# run sassy. If it fails, print a sad message :(
echo "$SASSY_CMD" | z3 -in || (echo "-----------------------"; echo "sassy failed :(")
