#!/bin/bash

ANALYSIS_DIR=$1
ANALYSIS_NAME=${ANALYSIS_DIR%-*}

./Imp.native --generate-constraints Imp/sassy-analyses/$ANALYSIS_DIR --lattice $ANALYSIS_NAME | python sassy-post-process.py
