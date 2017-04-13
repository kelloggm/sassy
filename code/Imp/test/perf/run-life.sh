#!/usr/bin/env bash

TDIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
IMP="${TDIR}/../../../Imp.native"

$IMP ${TDIR}/life-i.imp \
  | sed -e 's/[][,0]/ /g' \
        -e 's/1/*/g'
