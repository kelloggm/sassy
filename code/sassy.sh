#!/bin/bash

ANALYSIS_NAME=$1

./Imp.native --generate-constraints Imp/sassy-analyses/$ANALYSIS_NAME --lattice $ANALYSIS_NAME | python sassy-post-process.py
