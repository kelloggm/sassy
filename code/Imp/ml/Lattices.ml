open Lattice
open ZUtil

(* This contains the actual lattices we want to do the analysis on.

It'd be neat to be able to pull these out of a config file, but I didn't
want to write a new file format & lexing/parsing/etc.*)


(* TODO--do we need an abstraction function too?*)
let parity_lattice =
    let top = Element ((explode "@Both"), []) in
    let even = Element ((explode "@Even"), (top :: [])) in
    let odd = Element ((explode "@Odd"), (top :: [])) in
    let bottom = Element ((explode "@Bottom"), (even :: odd :: [])) in
    top :: even :: odd :: bottom :: []

let null_lattice =
    let maybe_null = Element ((explode "@PossiblyNull"), []) in
    let not_null = Element ((explode "@NotNull"), (maybe_null :: [])) in
    maybe_null :: not_null :: []

exception No_Such_Lattice of bytes

let get_lattice_by_name name =
    match name with
    | "parity" -> parity_lattice
    | "nullness" -> null_lattice
    | _ -> raise (No_Such_Lattice (mkstr "No lattice named %s." name))