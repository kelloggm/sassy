open ZUtil

type lattice_elt =
    | Element of char list * lattice_elt list

type lattice = lattice_elt list

let get_element_name elt = 
    match elt with
    | Element (n, _) -> n

let rec get_element_int lattice name =
    match lattice with
    | [] -> None
    | hd :: tl -> match hd with
                  | Element (n, _) -> if n=name then (Some hd) else get_element_int tl name

exception Element_not_found of bytes

let get_element lattice name =
    match (get_element_int lattice name) with
    | None -> raise (Element_not_found (mkstr "Unable to find element %s in the lattice." (implode name)))
    | Some n -> n

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

let get_all_up elt =
    let rec get_all_up_rec n e =
        match e with
        | Element (_, up) -> (e, n) :: (List.concat (List.map (get_all_up_rec (n+1)) up))
    in
        unique_elements (get_all_up_rec 0 elt)

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

let intersect li1 li2 =
    let p1 = List.filter (contains li2) li1 in
    let p2 = List.filter (contains li1) li2 in
    (elt_list_merge p1 p2)

exception Bad_Lub of bytes

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
    | hd :: tl -> hd
    | [] -> raise (Bad_Lub (mkstr "Unable to get a LUB of element %s and %s" (implode (get_element_name elt1)) (implode (get_element_name elt2))))

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