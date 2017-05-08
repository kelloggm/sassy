open ZUtil
open ImpSyntax
open ImpCommon
open ImpPretty

(* An abstract type is either an annotation,
or a basic op on an annotation.
This should be simplified later.
It can also be a constant; this is
used to generate constraints for the
abstraction function. *)
type abstr_type = 
    | Anno of char list
    | AOp1 of op1 * abstr_type
    | AOp2 of op2 * abstr_type * abstr_type
    | NoAnno
    | Constant of char list

let var_to_astore = function
    | Var v -> (v, NoAnno)
    | AnnoVar (a, v) -> (v, (Anno a))

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

let add_to_store_v var astore =
    add_to_store (var_to_astore var) astore

(* Merges two stores.  Currently arbitrarily chooses
the first store as 'true' if the stores disagree on a 
variable.  Long term that should be an error.*)
let rec merge_astores astore1 astore2 =
    match astore2 with
    | [] -> astore1
    | (name, anno) :: tl ->
        merge_astores (set_atype name anno astore1) tl

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
    | AnnoFunc of var * char list list * anno_stmt * anno_expr

type anno_prog =
    | AnnoProg of anno_func list * anno_stmt * anno_expr

(* Function environments look like abstract environments *)
type function_environment = (char list * abstr_type) list

(* Dataflow for expressions.
TODO:  Currently doesn't do anything to handle several 
built in 'expressions', and makes no attempt to handle 
stuff on the heap.
*)
let rec get_expr_atype expr astore =
    match expr with
    | Eval v -> Constant (explode (ImpPretty.expr_pretty expr)) (*TODO--This should use the abstraction function...*)
    | Evar var -> (match (get_atype var astore) with 
                 | None -> NoAnno (*TODO--This is use of a variable we haven't seen before*)
                 | Some a -> a)
    | Eop1 (op1, e1) -> AOp1 (op1, (get_expr_atype e1 astore)) (* TODO -- this is kind of a hack...*)
    | Eop2 (op2, e1, e2) -> AOp2 (op2, (get_expr_atype e1 astore), (get_expr_atype e2 astore))
    | Elen expr -> NoAnno (*TODO--Length expression takes an array and returns its length*)
    | Eidx (e1, e2) -> NoAnno (*TODO--Index expression gets a value from the heap.*)
    | Eanno (anno, expr) -> (Anno anno)

(* Abstract data flow of annotations for statements. *)
let rec dataflow_stmt stmt astore func_env = 
    match stmt with
    | Snop -> (AnnoStmt (stmt, astore))
    | Sset (x, e) ->
        let anno = (match x with
                    | Var v -> (v, (get_expr_atype e astore))
                    | AnnoVar (anno, v) -> (v, (Anno anno))) in
        (AnnoStmt (stmt, (add_to_store anno astore)))
    (* We'll probably want to update Alloc/Write to handle heap stuff somehow--this 
    just handles the pointer's annotation, if any. *)
    | Salloc (x, e1, e2) ->  
        (AnnoStmt (stmt, (add_to_store_v x astore)))
    | Swrite (x, e1, e2) -> 
        (AnnoStmt (stmt, (add_to_store_v x astore)))
    | Scall (x, f, es) ->
        let anno = match x with 
                    | AnnoVar (a, v) -> (v, (Anno a))
                    | Var v -> 
                        (match f with 
                        | AnnoVar (a, f) -> (v, (Anno a))
                        | Var f -> (match (get_atype f func_env) with
                                   | Some a -> (v, a)
                                   | None -> (v, NoAnno))
                        ) in
        (AnnoStmt (stmt, (add_to_store anno astore)))
    | Sifelse (e, p1, p2) -> 
        let true_path = (dataflow_stmt p1 astore func_env) in
        let false_path = (dataflow_stmt p2 astore func_env) in
        let merge_st = (merge_astores (anno_stmt_astore true_path) (anno_stmt_astore false_path)) in
        let final_st = (update_astore astore merge_st) in
        (Branch (e, true_path, false_path, final_st))
    | Swhile (e, p1) -> 
        let body = (dataflow_stmt p1 astore func_env) in
        let final_st = (update_astore astore (anno_stmt_astore body)) in
        (While (e, body, final_st))
    | Sseq (p1, p2) -> 
    let first = dataflow_stmt p1 astore func_env in
    Seq (first, (dataflow_stmt p2 (anno_stmt_astore first) func_env))

(* Map from functions to an entry in the function environment. 
Note that we only use annotations from the *name* of the function.
Mutual recursion makes figuring it out from the *)
let function_atype = function
    | Func(name, _, _, _) ->
        var_to_astore name

(* Create a 'parameters' abstract store for the inside
of a function. *)
let params_astore params =
    let create_empty param = (param, NoAnno)
    in List.map create_empty params

let dataflow_func func_env = function
    | Func (name, params, stmt, expr) ->
    let body = (dataflow_stmt stmt (params_astore params) func_env) in
    let return = AnnoExpr (expr, (get_expr_atype expr (anno_stmt_astore body))) in
    AnnoFunc (name, params, body, return)

let dataflow_prog = function
    | Prog (funcs, stmt, expr) ->
        let func_env = List.map function_atype funcs in
        let body = (dataflow_stmt stmt empty_abstr_store func_env) in
        let return = AnnoExpr (expr, (get_expr_atype expr (anno_stmt_astore body))) in
        AnnoProg 
            ((List.map (dataflow_func func_env) funcs),
            body,
            return)

(* Pretty Printing*)

let rec pretty_anno = function
    | Anno a -> implode a
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
    | AnnoFunc (name, params, anno_body, ret) ->
        mkstr "def %s(%s) {"
        (ImpPretty.var_pretty name)
        (params |> List.map implode
                |> String.concat ", ")
      :: indent (pretty_anno_stmt anno_body)
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
  | Anno (name) -> implode name
  | Constant (c) -> implode c
  | AOp1 (op, atypeInner) -> mkstr "(abstract-%s %s)" (op1_constraint_name op) (constraint_gen_abstr_type atypeInner)
  | AOp2 (op, atypeL, atypeR) -> mkstr "(abstract-%s %s %s)" (op2_constraint_name op) (constraint_gen_abstr_type atypeL) (constraint_gen_abstr_type atypeR)
  
let constraint_gen_set alhs arhs =
  match alhs with
  | Anno (alhsName) ->
     begin match arhs with
     | NoAnno -> mkstr ""
     | Constant (arhsConst) -> mkstr "(assert (= (abstract-abstraction %s) %s))" (implode arhsConst) (implode alhsName)
     | Anno (arhsName) -> mkstr "(assert (= (abstract-subtype %s %s) true))" (implode arhsName) (implode alhsName)
     | AOp1 (_,_) -> mkstr "(assert (= %s %s))" (constraint_gen_abstr_type arhs) (implode alhsName)
     | AOp2 (_,_,_) -> mkstr "(assert (= %s %s))" (constraint_gen_abstr_type arhs) (implode alhsName)
     end
  | _ -> mkstr ""
  
let rec constraint_gen_stmt = function
     | AnnoStmt (stmt, astore) ->
        begin match stmt with
         | Sset(x, e) ->
            let annoXOption = match x with
              | Var (name) -> get_atype name astore
              | AnnoVar (a, name) -> get_atype name astore in
            begin match annoXOption with
              | Some (annoX) ->  constraint_gen_set annoX (get_expr_atype e astore)
              | None -> mkstr "lhs unannotated. This situation is unimplemented."
            end
           
         | _ ->
            mkstr "stmt unimplemented"
        end
        :: [] (* <- note that all the strings above are being turned into lists! *)
    | Seq (s1, s2) -> 
        (constraint_gen_stmt s1)
        @ (constraint_gen_stmt s2)
    | Branch (condition_expr, true_stmt, false_stmt, astore) ->
        constraint_gen_stmt true_stmt @ constraint_gen_stmt false_stmt @ []
    | While (condition_expr, body_stmt, astore) ->
        constraint_gen_stmt body_stmt @ []
  
  
let constraint_gen_ret varOpt ret_expr =
  match varOpt with
  | None -> "" :: []
  | Some var ->
     match var with
     | Var(v) -> "" :: []
     | AnnoVar(a, v) -> constraint_gen_set (Anno a) (anno_expr_anno ret_expr) :: []
  
let constraint_gen_func' = function
  | AnnoFunc (name, params, anno_body, ret) ->
     constraint_gen_ret (Some name) ret @ constraint_gen_stmt anno_body @ []
  
let constraint_gen_func f =
  String.concat "\n" (constraint_gen_func' f)
  
let constraint_gen_prog' = function
  | AnnoProg (funcs, astmt, expr) ->
     List.map constraint_gen_func funcs
     @ constraint_gen_stmt astmt
    @ constraint_gen_ret None expr @ []
  
let constraint_gen_prog p =
  String.concat "\n" (constraint_gen_prog' p)

 
