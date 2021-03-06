open ZUtil
open ImpSyntax

(* Lattice element is an annotation and parents...*)
type lattice_elt =
    | Element of char list * lattice_elt list

type lattice = lattice_elt list

(* Get the name of a lattice element *)
let get_element_name elt = 
    match elt with
    | Element (n, _) -> n

(* Internal get-element (doesn't throw an exception)*)
let rec get_element_int lattice name =
    match lattice with
    | [] -> None
    | hd :: tl -> match hd with
                  | Element (n, _) -> if n=name then (Some hd) else get_element_int tl name

exception Element_not_found of bytes

(* Throws an exception if we can't find the element in the lattice. *)
let get_element lattice name =
    match (get_element_int lattice name) with
    | None -> raise (Element_not_found (mkstr "Unable to find element %s in the lattice." (implode name)))
    | Some n -> n


(* Gets unique elements from a list *)
let unique_elements elt_list =
    let rec uniq_helper elt li =
        match li with
        | [] -> []
        | hd :: tl -> if hd=elt then uniq_helper elt tl else hd :: uniq_helper elt tl
    in
    let rec uniq li =
        match li with
        | [] -> []
        | hd :: tl -> hd :: (uniq_helper hd (uniq tl)) 
    in
    uniq elt_list

(* Returns a list of everything "above" this lattice element--and the "height"
above the element that the other element is at. *)
let get_all_up elt =
    let rec get_all_up_rec n e =
        match e with
        | Element (_, up) -> (e, n) :: (List.concat (List.map (get_all_up_rec (n+1)) up))
    in
        unique_elements (get_all_up_rec 0 elt)

exception No_Top
      
(* Returns the top element in the lattice *)
let rec get_top lattice =
  match lattice with
  | hd :: tl -> begin match hd with Element(name,elts) ->
                  begin match elts with
                  | [] -> name
                  | h :: t -> get_top tl
                  end
                end
  | [] -> raise No_Top
              
(* Returns the bottom element(s) in the lattice *)
let get_bots lattice =
  let rec all_with_subtype lat acc =
    match lat with [] -> acc
                 | hd :: tl ->
                    match hd with Element(_, up) -> all_with_subtype tl (up @ acc)
  in
  let elts_with_subtype = unique_elements (all_with_subtype lattice []) in
  let bot_types = List.filter (fun x -> not (List.mem x elts_with_subtype)) lattice in
  let bot_names = List.map get_element_name bot_types in
  String.concat ", " (List.map implode bot_names)
                            
(* Bunch of helper functions for LUB *)
let elt_eq elt1 elt2=
    match elt1 with
    | (e1, _) -> 
        match elt2 with
        | (e2, _) -> e1=e2

let rec contains li elt =
    match li with
    | [] -> false
    | hd :: tl -> if elt_eq hd elt then true else (contains tl elt)

let add_elt elt1 elt2 = 
    match elt1 with
    | (e, n1) -> match elt2 with
                | (_, n2) -> (e, n1+n2)

(* Merges two lists of (element, height)--adds the height of matching elements.*)
let elt_list_merge li1 li2 =
    let rec find_match elt li =
        match li with
        | [] -> elt
        | hd :: tl -> if (elt_eq hd elt) then (add_elt hd elt) else find_match elt tl
    in
    let rec merge li1 li2 =
        match li1 with
        | [] -> []
        | hd :: tl -> (find_match hd li2) :: merge tl li2
    in
    merge li1 li2

(* Intersects two lists of (element, height) by adding the heights.*)
let intersect li1 li2 =
    let p1 = List.filter (contains li2) li1 in
    let p2 = List.filter (contains li1) li2 in
    (elt_list_merge p1 p2)

exception Bad_Lub of bytes

(* LUB for two lattice elements.

E.x1 Even, Odd
e.x2 Even, Even

Basically, we get the set of all elements "over"
each element, plus the elements themselves.  We 
assign a "height" over the elements (# of steps).
E.x1
Even -> (Even, 0), (Both, 1)
Odd -> (Odd, 0), (Both, 1)

e.x2 -> (Even, 0), (Both, 1)


Then we take the intersection (elements over both of them)
and add the heights (to produce an order).
E.x1 (Both, 2) -> Both is LUB.
E.x2 (Even, 0), (Both, 2) -> Even is LUB.

I'm not certain this works for every lattice, but it definitely works
for the ones we're interested in.
*)
let lub elt1 elt2 =
    let up1 = get_all_up elt1 in
    let up2 = get_all_up elt2 in
    let intersection = intersect up1 up2 in
    let get_depth el =
        match el with
        | (elt, n) -> n
    in
    let compare el1 el2 = (get_depth el1) - (get_depth el2) in
    match List.sort compare intersection with
    | (hd,_) :: tl -> hd
    | [] -> raise (Bad_Lub (mkstr "Unable to get a LUB of element %s and %s" (implode (get_element_name elt1)) (implode (get_element_name elt2))))

let get_elts lattice =
  String.concat " " (List.map (fun x -> (implode (get_element_name x))) lattice)
  
(* 
 * Generate the smt2 code to send to z3 that defines a lattice.
 * Returns a list of strings, each of which is a constraint.
 *)
let generate_lattice_constraints lattice =
  mkstr "(declare-datatypes () ((Elt %s)))\n;Top: %s\n;Bottom: %s\n;Elts:~%s" (get_elts lattice) (implode (get_top lattice)) (get_bots lattice) (get_elts lattice) :: []

(* Abstract interpretation is a lattice and an abstraction function *)
type abstract_interpretation =
    lattice * (coq_val -> lattice_elt)

let get_lattice abstr_interp = 
    match abstr_interp with
    | (lat, abstr) -> lat

let get_abstraction_function abstr_interp =
    match abstr_interp with
    | (lat, abstr) -> abstr
