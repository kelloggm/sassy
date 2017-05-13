open ZUtil
open ImpSyntax
open ImpCommon

let val_pretty = function
  | Vbool true -> "True"
  | Vbool false -> "False"
  | Vint i -> Big.to_string i
  | Vstr s -> mkstr "\"%s\"" (String.escaped (implode s))
  | Vaddr a -> mkstr "(Vaddr %s)" (Big.to_string a)

let var_pretty = function
  | Var v -> (implode v)
  | AnnoVar (a, v) -> mkstr "[(%s) %s]" (implode a) (implode v)

let op1_pretty = function
  | Oneg -> "-"
  | Onot -> "not"

let op2_pretty = function
  | Oadd -> "+"
  | Osub -> "-"
  | Omul -> "*"
  | Odiv -> "/"
  | Omod -> "%"
  | Oeq -> "=="
  | Olt -> "<"
  | Ole -> "<="
  | Oconj -> "and"
  | Odisj -> "or"

let rec expr_pretty = function
  | Eval v ->
      val_pretty v
  | Evar x ->
      implode x
  | Eop1 (op, e1) ->
      mkstr "(%s %s)"
        (op1_pretty op)
        (expr_pretty e1)
  | Eop2 (op, e1, e2) ->
      mkstr "(%s %s %s)"
        (expr_pretty e1)
        (op2_pretty op)
        (expr_pretty e2)
  | Elen e1 ->
      mkstr "len(%s)" (expr_pretty e1)
  | Eidx (e1, e2) ->
      mkstr "(%s[%s])"
        (expr_pretty e1)
        (expr_pretty e2)
  | Eanno (str, e1) ->
      mkstr "(%s [%s])"
        (implode str)
        (expr_pretty e1)

let indent ls =
  List.map (fun l -> "  " ^ l) ls

let anno_mem_pretty = function
  | AnnoEq (v, a) -> (mkstr "%s = %s" (implode v) (implode a))


let rec anno_store_pretty = function
  | AnnoSt a -> (anno_mem_pretty a) :: []
  | AnnoSeq (a, rest) -> (anno_mem_pretty a) :: (anno_store_pretty rest)

let rec stmt_pretty' = function
  | Snop ->
      "nop;" :: []
  | Sset (x, e) ->
      mkstr "%s = %s;"
        (var_pretty x)
        (expr_pretty e)
      :: []
  | Salloc (x, e1, e2) ->
      mkstr "%s = alloc(%s, %s);"
        (var_pretty x)
        (expr_pretty e1)
        (expr_pretty e2)
      :: []
  | Swrite (x, e1, e2) ->
      mkstr "%s[%s] = %s;"
        (var_pretty x)
        (expr_pretty e1)
        (expr_pretty e2)
      :: []
  | Scall (x, f, es) ->
      mkstr "%s = %s(%s);"
        (var_pretty x)
        (var_pretty f)
        (es |> List.map expr_pretty
            |> String.concat ", ")
      :: []
  | Sifelse (e, p1, p2) ->
      mkstr "if %s {" (expr_pretty e)
        :: indent (stmt_pretty' p1)
      @ "} else {"
        :: indent (stmt_pretty' p2)
      @ "}" :: []
  | Swhile (e, p1) ->
      mkstr "while %s {" (expr_pretty e)
        :: indent (stmt_pretty' p1)
      @ "}" :: []
  | Sseq (p1, p2) ->
      stmt_pretty' p1 @ stmt_pretty' p2
  | AStmt (st, p1) ->
      "[ " :: (anno_store_pretty st) @ " ]"
      :: stmt_pretty' p1

let stmt_pretty s =
  String.concat "\n" (stmt_pretty' s)

let func_pretty' = function
  | Func (name, params, body, ret) ->
      mkstr "def %s(%s) {"
        (var_pretty name)
        (params |> List.map var_pretty
                |> String.concat ", ")
      :: indent (stmt_pretty' body)
      @  indent ((mkstr "return %s;" (expr_pretty ret)) :: [])
      @  "}" :: []

let func_pretty f =
  String.concat "\n" (func_pretty' f)

let prog_pretty' = function
  | Prog (funcs, body, ret) ->
      List.map func_pretty funcs
      @ stmt_pretty' body
      @ mkstr "return %s;" (expr_pretty ret)
      :: []

let prog_pretty p =
  String.concat "\n" (prog_pretty' p)

let store_pretty s =
  s |> List.map
        (function (x, v) ->
          mkstr "%s = %s" (implode x) (val_pretty v))
    |> String.concat "\n"

let heap_pretty h =
  h |> List.mapi
        (fun i v ->
          mkstr "%d : %s" i (val_pretty v))
    |> String.concat "\n"

let rec array_pretty h a =
  if Big.lt a Big.zero
  || Big.le (big_len h) a then
    failwith "array_pretty bogus pointer"
  else
    match big_nth h a with
    | Vint n ->
        if Big.lt n Big.zero
        || Big.le (big_len h) (Big.add a n) then
          failwith "array_pretty bogus array"
        else
          n |> big_range
            |> List.map (fun i -> Big.add a (Big.add i Big.one))
            |> List.map (big_nth h)
            |> List.map (function Vaddr a -> array_pretty h a
                                | v -> val_pretty v)
            |> String.concat ", "
            |> mkstr "[%s]"
    | v ->
        failwith "array_pretty pointer to non-array"

let result_pretty = function
  | Some (h, v) ->
      begin match v with
      | Vaddr a -> array_pretty h a
      | Vstr cs -> implode cs
      | v -> val_pretty v
      end
  | None -> "Stuck or Timeout"
