#!/usr/bin/python

# A post-processor for sassy's constraint generation phase. Takes as input
# a list of lines, some of which contain constraints and some of which are
# blank. Removes all blank lines and then creates a dictionary of constants
# based on constraints generated on the abstract-abstraction function.
# Replaces constants that appear in other constraints with the type that
# the abstract-abstraction function must give them. Emits the result.

# Type abbreviation dictionary:
#
# rg - list
# ln - string of input/output
# zcs - z3 constraint string
# lcn - literal constant
# lae - lattice element

import fileinput

rgzcs = []

mplcn_lae = {}

for ln in fileinput.input():
    ln = ln.strip()
    if ln:
        if "abstract-abstraction" in ln:
            rgst = ln.split()
            lcn = rgst[3].replace(")", "")
            lae = rgst[4].replace(")", "")
            mplcn_lae[lcn] = lae
        
        rgzcs.append(ln)

rgzcsFiltered = []
        
for zcs in rgzcs:
    for lcn in mplcn_lae.keys():
        if " " + lcn in zcs and not "abstract-abstraction" in zcs:
            zcs = zcs.replace(lcn, mplcn_lae[lcn])

    if zcs not in rgzcsFiltered:
        rgzcsFiltered.append(zcs)

rgzcsFiltered.sort()
        
for zcs in rgzcsFiltered:
    print zcs
