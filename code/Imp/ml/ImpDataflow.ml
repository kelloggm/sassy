open ZUtil
open ImpSyntax
open ImpCommon
open ImpPretty
open Lattice

(* TODO--make this work with lattices*)

(* An abstract type is either an annotation,
or a basic op on an annotation.
This should be simplified later.
It can also be a constant; this is
used to generate constraints for the
abstraction function. *)
type abstr_type = 
    | Anno of lattice_elt
    | AOp1 of op1 * abstr_type
    | AOp2 of op2 * abstr_type * abstr_type
    | NoAnno
    | Constant of char list

let get_anno lattice anno =
    Anno (get_element lattice anno)

let var_to_astore lattice = function
    | Var v -> (v, NoAnno)
    | AnnoVar (a, v) -> (v, (get_anno lattice a))

(* Abstract store is just a list of pairs *)
type abstr_store_val = (char list * abstr_type)

type abstr_store = abstr_store_val list

let empty_abstr_store = []

(* Gets/Sets for mapping (varname) to abstract stores *)
let rec get_atype var astore =
    match astore with
    | [] -> None
    | (name, anno) :: tl -> 
        (if name=var then (Some anno) else (get_atype var tl))

let rec set_atype var anno astore =
    match astore with
    | [] -> (var, anno) :: []
    | (name, oanno) :: tl ->
        (if name=var 
        then (name, anno) :: tl
        else (name, oanno) :: (set_atype var anno tl))

(* Adds a var to the store*)
let add_to_store var astore =
    match var with
    | (name, anno) -> set_atype name anno astore

let add_to_store_v lattice var astore =
    add_to_store (var_to_astore lattice var) astore



let rec set_atype_lub lattice var anno astore =
    let rec get_anno_lub oanno =
        match anno with
        | Anno a1 -> (match oanno with 
                        | Anno a2 -> Anno (Lattice.lub a1 a2)
                        | Constant c -> anno (* Unclear how to do LUB here.*)
                        | AOp1 (op, a) -> anno (* Unclear how to do LUB here.*)
                        | AOp2 (op, a1, a2) -> anno (* Unclear how/if we want to do LUB here.*)
                        | NoAnno -> anno)
        | _ -> anno
    in
    match astore with
    | [] -> (var, anno) :: []
    | (name, oanno) :: tl ->
        (if name=var 
        then (name, (get_anno_lub oanno)) :: tl
        else (name, oanno) :: (set_atype_lub lattice var anno tl))

(* Merges two stores, taking the LUB when two elements overlap.*)
let rec merge_astores_lub lattice astore1 astore2 =
    match astore2 with
    | [] -> astore1
    | (name, anno) :: tl -> 
            merge_astores_lub lattice (set_atype_lub lattice name anno astore1) tl


(* Merges two stores.  Currently arbitrarily chooses
the first store as 'true' if the stores disagree on a 
variable. This is the correct behavior for some things.*)
let rec merge_astores_first_wins astore1 astore2 =
    match astore2 with
    | [] -> astore1
    | (name, anno) :: tl ->
        merge_astores_first_wins (set_atype name anno astore1) tl

(* Updates a store with any changes to the abstract type
of variables inside a 'smaller' scope (if/while).  
I.e. if we set the abstract type in a while, we 
update it.  If a variable is local to the while,
then we drop it. *)
let rec update_astore old_astore sub_astore =
    match sub_astore with
    | [] -> old_astore
    | (var, anno) :: tl -> 
        match (get_atype var old_astore) with
        | None -> (update_astore old_astore tl)
        | Some a -> (update_astore (set_atype var anno old_astore) tl)

(* Annotated expressions/statements/etc. *)
type anno_expr =
    | AnnoExpr of expr * abstr_type

let anno_expr_expr = function
    | AnnoExpr (e, a) -> e 

let anno_expr_anno = function 
    | AnnoExpr (e, a) -> a

type anno_stmt = 
    | AnnoStmt of stmt * abstr_store
    | Seq of anno_stmt * anno_stmt
    | Branch of expr * anno_stmt * anno_stmt * abstr_store
    | While of expr * anno_stmt * abstr_store

let rec anno_stmt_astore = function
    | AnnoStmt (stmt, astore) -> astore
    | Seq (a1, a2) -> (anno_stmt_astore a2)
    | Branch (e, p1, p2, st) -> st
    | While (e, a1, st) -> st

type anno_func =
    | AnnoFunc of var * var list * abstr_store * anno_stmt * anno_expr

type anno_prog =
    | AnnoProg of anno_func list * anno_stmt * anno_expr

(* Function environments look like abstract environments *)
type function_environment = (char list * abstr_type) list

(* Dataflow for expressions.
TODO:  Currently doesn't do anything to handle several 
built in 'expressions', and makes no attempt to handle 
stuff on the heap.
*)
let rec get_expr_atype lattice expr astore =
    match expr with
    | Eval v -> Constant (explode (ImpPretty.expr_pretty expr)) (*TODO--This should use the abstraction function...*)
    | Evar var -> (match (get_atype var astore) with 
                 | None -> NoAnno (*TODO--This is use of a variable we haven't seen before*)
                 | Some a -> a)
    | Eop1 (op1, e1) -> AOp1 (op1, (get_expr_atype lattice e1 astore)) (* TODO -- this is kind of a hack...*)
    | Eop2 (op2, e1, e2) -> AOp2 (op2, (get_expr_atype lattice e1 astore), (get_expr_atype lattice e2 astore))
    | Elen expr -> NoAnno (*TODO--Length expression takes an array and returns its length*)
    | Eidx (e1, e2) -> NoAnno (*TODO--Index expression gets a value from the heap.*)
    | Eanno (anno, expr) -> (get_anno lattice anno)

let get_astore_anno lattice = function 
    | AnnoEq (v, a) -> (v, (get_anno lattice a))

let rec update_from_astore lattice anno_st astore = 
    match anno_st with
    | AnnoSt a -> add_to_store (get_astore_anno lattice a) astore
    | AnnoSeq (a, r) -> 
        (merge_astores_first_wins (update_from_astore lattice r astore) (add_to_store (get_astore_anno lattice a) astore))

(* Abstract data flow of annotations for statements. *)
let rec dataflow_stmt lattice stmt astore func_env = 
    match stmt with
    | Snop -> (AnnoStmt (stmt, astore))
    | Sset (x, e) ->
        let anno = (match x with
                    | Var v -> (v, (get_expr_atype lattice e astore))
                    | AnnoVar (anno, v) -> (v, (get_anno lattice anno))) in
        (AnnoStmt (stmt, (add_to_store anno astore)))
    (* We'll probably want to update Alloc/Write to handle heap stuff somehow--this 
    just handles the pointer's annotation, if any. *)
    | Salloc (x, e1, e2) ->  
        (AnnoStmt (stmt, (add_to_store_v lattice x astore)))
    | Swrite (x, e1, e2) -> 
        (AnnoStmt (stmt, (add_to_store_v lattice x astore)))
    | Scall (x, f, es) ->
        let anno = match x with 
                    | AnnoVar (a, v) -> (v, (get_anno lattice a))
                    | Var v -> 
                        (match f with 
                        | AnnoVar (a, f) -> (v, (get_anno lattice a))
                        | Var f -> (match (get_atype f func_env) with
                                   | Some a -> (v, a)
                                   | None -> (v, NoAnno))
                        ) in
        (AnnoStmt (stmt, (add_to_store anno astore)))
    | Sifelse (e, p1, p2) -> 
        let true_path = (dataflow_stmt lattice p1 astore func_env) in
        let false_path = (dataflow_stmt lattice p2 astore func_env) in
        let merge_st = (merge_astores_lub lattice (anno_stmt_astore true_path) (anno_stmt_astore false_path)) in
        let final_st = (update_astore astore merge_st) in
        (Branch (e, true_path, false_path, final_st))
    | Swhile (e, p1) -> 
        let body = (dataflow_stmt lattice p1 astore func_env) in
        let final_st = (update_astore astore (anno_stmt_astore body)) in
        (While (e, body, final_st))
    | Sseq (p1, p2) -> 
    let first = dataflow_stmt lattice p1 astore func_env in
    Seq (first, (dataflow_stmt lattice p2 (anno_stmt_astore first) func_env))
    | AStmt (anno_st, p1) -> 
        (dataflow_stmt lattice p1 (update_from_astore lattice anno_st astore) func_env) (* TODO--Actually use these annotations...*)

(* Map from functions to an entry in the function environment. 
Note that we only use annotations from the *name* of the function.
Mutual recursion makes figuring it out from the *)
let function_atype lattice = function
    | Func(name, _, _, _) ->
        var_to_astore lattice name

(* Create a 'parameters' abstract store for the inside
of a function. *)
let params_astore lattice params =
    List.map (var_to_astore lattice) params

let dataflow_func lattice func_env = function
    | Func (name, params, stmt, expr) ->
    let abstr_store = (params_astore lattice params) in
    let body = (dataflow_stmt lattice stmt abstr_store func_env) in
    let return = AnnoExpr (expr, (get_expr_atype lattice expr (anno_stmt_astore body))) in
    AnnoFunc (name, params, abstr_store, body, return)

let dataflow_prog lattice = function
    | Prog (funcs, stmt, expr) ->
        let func_env = List.map (function_atype lattice) funcs in
        let body = (dataflow_stmt lattice stmt empty_abstr_store func_env) in
        let return = AnnoExpr (expr, (get_expr_atype lattice expr (anno_stmt_astore body))) in
        AnnoProg 
            ((List.map (dataflow_func lattice func_env) funcs),
            body,
            return)

(* Pretty Printing*)

let rec pretty_anno = function
    | Anno a -> (implode (get_element_name a))
    | Constant c -> implode c
    | AOp1 (op1, a1) ->
        mkstr "(%s %s)"
        (ImpPretty.op1_pretty op1) 
        (pretty_anno a1)
    | AOp2 (op2, a1, a2) -> 
        mkstr "(%s %s %s)"
            (pretty_anno a1)
            (ImpPretty.op2_pretty op2)
            (pretty_anno a2)
    | NoAnno -> mkstr "#NoAnno"


let pr_astore_st acc curr_st  =
    match curr_st with
    (var, anno) ->
        String.concat ""
        (acc :: (implode var) :: "::" :: (pretty_anno anno) :: "\n" :: [])

let pretty_astore astore =
    String.concat "" 
    ("[[\n" :: 
    (List.fold_left pr_astore_st "" astore) 
    :: "]]" :: [])

let rec pretty_anno_stmt = function
    | AnnoStmt (st, astore) ->
        mkstr "%s \n %s" 
        (ImpPretty.stmt_pretty st) 
        (pretty_astore astore)
        :: []
    | Seq (s1, s2) -> 
        (pretty_anno_stmt s1)
        @ (pretty_anno_stmt s2)
    | Branch (e, ts, fs, st) ->
        (mkstr "if %s {" (expr_pretty e))
        :: indent (pretty_anno_stmt ts)
        @ "} else {" 
        :: indent (pretty_anno_stmt fs) @ "}" ::
        (pretty_astore st) :: []
    | While (e, b, st) ->
        "while (" :: (expr_pretty e) :: ")" ::
        (pretty_anno_stmt b) @
        (pretty_astore st) :: []

let pretty_dataflow_func' = function
    | AnnoFunc (name, params, abstr_store, anno_body, ret) ->
        mkstr "def %s(%s) {"
        (ImpPretty.var_pretty name)
        (params |> List.map ImpPretty.var_pretty
                |> String.concat ", ")
      :: indent ((pretty_astore abstr_store) :: [])
      @ indent (pretty_anno_stmt anno_body)
      @ indent ((mkstr "return %s;" (ImpPretty.expr_pretty (anno_expr_expr ret))) :: [])
      @ mkstr "[[ return :: %s ]]" (pretty_anno (anno_expr_anno ret))
      :: "}" :: []

let pretty_dataflow_func f =
    String.concat "\n" (pretty_dataflow_func' f)

let pretty_dataflow_prog' = function
    | AnnoProg (funcs, astmt, expr) ->
    List.map pretty_dataflow_func funcs
    @ pretty_anno_stmt astmt
    @ mkstr "return %s" (ImpPretty.expr_pretty (anno_expr_expr expr))
    :: mkstr "[[ return :: %s ]]" (pretty_anno (anno_expr_anno expr))
    :: []

let pretty_dataflow_prog p = 
  String.concat "\n" (pretty_dataflow_prog' p)


(* constraint generation *)

(* 
 * unwraps a pair of options and passes them to f 
 * if either is None, returns the empty string
 * otherwise, returns the result of calling f 
 *
let unwrap f opt1 opt2 =
  match opt1 with
  | Some x ->
     begin match opt2 with
     | Some y -> f x y
     | None -> ""
     end
  | None -> ""*)

(* 
   AOp1 and AOp2 contain an operation and two abstract types, not annotations.
   So we need another layer of recursion here: constraint_gen_set needs to
   call something that produces lisp-y code for their subterms.
 *)

let op1_constraint_name = function
  | Oneg -> "negate"
  | Onot -> "not"

let op2_constraint_name = function
  | Oadd -> "plus"
  | Osub -> "minus"
  | Omul -> "times"
  | Odiv -> "divide"
  | Omod -> "mod"
  | Oeq -> "eq"
  | Olt -> "lt"
  | Ole -> "lte"
  | Oconj -> "and"
  | Odisj -> "or"

let rec constraint_gen_abstr_type atype =
  match atype with
  | NoAnno -> mkstr "" (* is this the right thing to do? *)
  | Anno (elt) -> implode (get_element_name elt)
  | Constant (c) -> implode c
  | AOp1 (op, atypeInner) -> mkstr "(abstract-%s %s)" (op1_constraint_name op) (constraint_gen_abstr_type atypeInner)
  | AOp2 (op, atypeL, atypeR) -> mkstr "(abstract-%s %s %s)" (op2_constraint_name op) (constraint_gen_abstr_type atypeL) (constraint_gen_abstr_type atypeR)
  
let constraint_gen_set alhs arhs =
  match alhs with
  | Anno (alhsElt) ->
     begin match arhs with
     | NoAnno -> mkstr ""
     | Constant (arhsConst) -> mkstr "(assert (= (abstract-abstraction %s) %s))" (implode arhsConst) (implode (get_element_name alhsElt))
     | Anno (arhsElt) -> mkstr "(assert (= (abstract-subtype %s %s) true))" (implode (get_element_name arhsElt)) (implode (get_element_name alhsElt))
     | AOp1 (_,_) -> mkstr "(assert (= %s %s))" (constraint_gen_abstr_type arhs) (implode (get_element_name alhsElt))
     | AOp2 (_,_,_) -> mkstr "(assert (= %s %s))" (constraint_gen_abstr_type arhs) (implode (get_element_name alhsElt))
     end
  | _ -> mkstr ""

let find_name_of_expr expr =
  match expr with
        | Eval(v) -> explode (ImpPretty.expr_pretty expr)
        | Evar(x) -> explode (ImpPretty.expr_pretty expr)
        | _ -> explode "$invalid: unimplemented$3"

let unwrap_expr_type etype =
  match etype with
  | Anno (elt) -> implode (get_element_name elt)
  | Constant (c) -> implode c
  | _ -> "$invalid: unimplemented$1"

let emit_constraint_if op lhs_type rhs_type expr_type constraint_name =
  mkstr "(assert (= (abstract-if-%s-%s %s %s) %s))" constraint_name (op2_constraint_name op) lhs_type rhs_type expr_type
             
let constraint_gen_if lattice cexpr tstmt fstmt astore =
  match cexpr with
  | Eop2 (op, lhs, rhs) -> begin
      let then_store = anno_stmt_astore tstmt in
      let else_store = anno_stmt_astore fstmt in
      (* any of these types can be None *)
      let lhs_then_type = unwrap_expr_type (get_expr_atype lattice lhs then_store) in
      let lhs_else_type = unwrap_expr_type (get_expr_atype lattice lhs else_store) in
      let rhs_then_type = unwrap_expr_type (get_expr_atype lattice rhs then_store) in
      let rhs_else_type = unwrap_expr_type (get_expr_atype lattice rhs else_store) in
      let lhs_type = unwrap_expr_type (get_expr_atype lattice lhs astore) in
      let rhs_type = unwrap_expr_type (get_expr_atype lattice rhs astore) in
      emit_constraint_if op lhs_type rhs_type lhs_then_type "then-store-lhs" ::
      emit_constraint_if op lhs_type rhs_type lhs_else_type "else-store-lhs" ::
      emit_constraint_if op lhs_type rhs_type rhs_then_type "then-store-rhs" ::
      emit_constraint_if op lhs_type rhs_type rhs_else_type "else-store-rhs" ::
          []
    end
  | _ -> mkstr "" :: []                      
       
let rec constraint_gen_stmt lattice anno_stmt =
  match anno_stmt with
     | AnnoStmt (stmt, astore) ->
        begin match stmt with
         | Sset(x, e) ->
            let annoXOption = match x with
              | Var (name) -> get_atype name astore
              | AnnoVar (a, name) -> get_atype name astore in
            begin match annoXOption with
              | Some (annoX) ->  constraint_gen_set annoX (get_expr_atype lattice e astore)
              | None -> mkstr "lhs unannotated. This situation is unimplemented."
            end
         | Scall(x, f, es) ->
         (* Do nothing? It looks like we're already handling this correctly. *)
            mkstr ""
         | _ ->
            mkstr "stmt unimplemented: %s" (String.concat "\n" (List.map Bytes.to_string (pretty_anno_stmt anno_stmt)))
        end
        :: [] (* <- note that all the strings above are being turned into lists! *)
    | Seq (s1, s2) -> 
        (constraint_gen_stmt lattice s1)
        @ (constraint_gen_stmt lattice s2)
    | Branch (condition_expr, true_stmt, false_stmt, astore) ->
       constraint_gen_if lattice condition_expr true_stmt false_stmt astore @
       constraint_gen_stmt lattice true_stmt
       @ constraint_gen_stmt lattice false_stmt @ []
    | While (condition_expr, body_stmt, astore) ->
        constraint_gen_stmt lattice body_stmt @ []
  
  
let constraint_gen_ret lattice varOpt ret_expr =
  match varOpt with
  | None -> "" :: []
  | Some var ->
     match var with
     | Var(v) -> "" :: []
     | AnnoVar(a, v) -> constraint_gen_set (get_anno lattice a) (anno_expr_anno ret_expr) :: []
  
let constraint_gen_func' lattice = function
  | AnnoFunc (name, params, abstract_store, anno_body, ret) ->
     constraint_gen_ret lattice (Some name) ret
     @ constraint_gen_stmt lattice anno_body @ []
  
let constraint_gen_func lattice f =
  String.concat "\n" (constraint_gen_func' lattice f)
  
let constraint_gen_prog' lattice = function
  | AnnoProg (funcs, astmt, expr) ->
     List.map (constraint_gen_func lattice) funcs
     @ constraint_gen_stmt lattice astmt
    @ constraint_gen_ret lattice None expr @ []
  
let constraint_gen_prog lattice p =
  String.concat "\n" (constraint_gen_prog' lattice p)

 
