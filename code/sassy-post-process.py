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
# zdf - z3 define/declare string
# zas - z3 assertion string
# lcn - literal constant
# lae - lattice element
# btf - binary transfer function
# utf - unary transfer function
# tel - top element in lattice
# bel - bottom element in lattice

import fileinput

rgzas = []
rgzdf = []

rgbtf = ["plus", "minus", "times", "divide", "mod", "eq", "lt", "lte", "and", "or"]
rgutf = ["negate", "not"]

tel = ""
rgbel = []

mplcn_lae = {}

rglae = []

for ln in fileinput.input():
    ln = ln.strip()
    if ln:
        if ln.startswith("(assert"):
            if "abstract-abstraction" in ln:
                rgst = ln.split()
                lcn = rgst[3].replace(")", "")
                lae = rgst[4].replace(")", "")
                mplcn_lae[lcn] = lae
        
            rgzas.append(ln)
        elif ln.startswith(";Top: "):
            tel = ln.split()[1].strip()
        elif ln.startswith(";Bottom: "):
            for bel in ln.split()[1].split(", "):
                rgbel.append(bel)
        elif ln.startswith(";Elts:~"):
            for lae in ln.split("~")[1].split(" "):
                rglae.append(lae)
        else:
            rgzdf.append(ln)
                
rgzasFiltered = []
        
for zas in rgzas:
    for lcn in mplcn_lae.keys():
        if " " + lcn in zas and not "abstract-abstraction" in zas:
            zas = zas.replace(lcn, mplcn_lae[lcn])

    if zas not in rgzasFiltered:
        rgzasFiltered.append(zas)

rgzasFiltered.sort()

for zdf in rgzdf:
    print zdf

for utf in rgutf:
    print "(declare-fun abstract-" + utf + " (Elt) Elt)"

for btf in rgbtf:
    print "(declare-fun abstract-" + btf + " (Elt Elt) Elt)"

print "(declare-fun abstract-subtype (Elt Elt) Bool)"
print "(declare-fun abstract-abstraction (Int) Elt)"
    
for zas in rgzasFiltered:
    print zas
    
# generic constraints on unary transfer functions
for utf in rgutf:
    print "(assert (= (abstract-" + utf + " " + tel + ") " + tel + "))"
    for bel in rgbel:
        print "(assert (= (abstract-" + utf + " " + bel + ") " + bel + "))"
    for lae in rglae:
        print "(assert-soft (= (abstract-" + utf + " " + lae + ") " + tel + "))"

# generic constraints on binary transfer functions
for btf in rgbtf:
    print "(assert (= (abstract-" + btf + " " + tel + " " + tel + ") " + tel + "))"
    for bel in rgbel:
        print "(assert (= (abstract-" + btf + " " + bel + " " + bel + ") " + bel + "))"
    for lae1 in rglae:
        for lae2 in rglae:
            if lae1 in rgbel:
                print "(assert-soft (= (abstract-" + btf + " " + lae1 + " " + lae2 + ") " + lae1 + "))"
            elif lae2 in rgbel:
                 print "(assert-soft (= (abstract-" + btf + " " + lae1 + " " + lae2 + ") " + lae2 + "))"
            else:
                print "(assert-soft (= (abstract-" + btf + " " + lae1 + " " + lae2 + ") " + tel + "))"
    
print "(check-sat)"
print "(get-model)"
