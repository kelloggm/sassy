open Lattice
open ZUtil
open ImpSyntax

(* This contains the actual lattices we want to do the analysis on.

It'd be neat to be able to pull these out of a config file, but I didn't
want to write a new file format & lexing/parsing/etc.*)


(* TODO--do we need an abstraction function too?*)
let parity_lattice =
    let top = Element ((explode "@Both"), []) in
    let even = Element ((explode "@Even"), (top :: [])) in
    let odd = Element ((explode "@Odd"), (top :: [])) in
    let bottom = Element ((explode "@Bottom"), (even :: odd :: [])) in
    let abstraction_function = function
        | Vint i -> 
            let big_mod = (Big_int.mod_big_int i (Big_int.big_int_of_int 2))
            in
                (if (Big_int.compare_big_int big_mod Big_int.zero_big_int) = 0 then even else odd)
        | _ -> bottom
    in
    ((top :: even :: odd :: bottom :: []), abstraction_function)

let null_lattice =
    let maybe_null = Element ((explode "@PossiblyNull"), []) in
    let not_null = Element ((explode "@NotNull"), (maybe_null :: [])) in
    let abstraction_function = function
        | Vaddr a -> not_null
        | _ -> maybe_null
    in
    ((maybe_null :: not_null :: []), abstraction_function)

let sign_lattice =
    let top = Element ((explode "@Top"), []) in
    let poszero = Element ((explode "@PosOrZero"), (top :: [])) in
    let negzero = Element ((explode "@NegOrZero"), (top :: [])) in
    let pos = Element ((explode "@Positive"), (poszero :: [])) in
    let neg = Element ((explode "@Negative"), (negzero :: [])) in
    let zero = Element ((explode "@Zero"), (poszero :: negzero :: [])) in
    let bottom = Element ((explode "@Bottom"), (pos :: neg :: zero :: [])) in
    let abstraction_function = function
        | Vint i -> 
            (match (Big_int.sign_big_int i) with
            | 0 -> zero
            | -1 -> neg
            | 1 -> pos
            | _ -> top)
        | _ -> bottom
    in
    ((top :: poszero :: negzero :: pos :: zero :: neg :: bottom :: []), abstraction_function)


exception No_Such_Lattice of bytes

let get_lattice_by_name name =
    match name with
    | "parity" -> parity_lattice
    | "nullness" -> null_lattice
    | "sign" -> sign_lattice
    | _ -> raise (No_Such_Lattice (mkstr "No lattice named %s." name))