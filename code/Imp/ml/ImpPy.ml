open ZUtil
open ImpSyntax
open ImpCommon

let indent ls =
  List.map (fun l -> "  " ^ l) ls

let var_py = function
  | Var v -> (implode v)
  | AnnoVar (a, v) -> (implode v)

let rec expr_py = function
  | Eval v ->
      ImpPretty.val_pretty v
  | Evar x ->
      implode x
  | Eop1 (op, e1) ->
      mkstr "(%s %s)"
        (ImpPretty.op1_pretty op)
        (expr_py e1)
  | Eop2 (op, e1, e2) ->
      mkstr "(%s %s %s)"
        (expr_py e1)
        (ImpPretty.op2_pretty op)
        (expr_py e2)
  | Elen e1 ->
      mkstr "len(%s)" (expr_py e1)
  | Eidx (e1, e2) ->
      mkstr "(%s[%s])"
        (expr_py e1)
        (expr_py e2)
  | Eanno (str, e1) ->
      mkstr "%s" (expr_py e1)


let rec stmt_py' = function
  | Snop ->
      []
  | Sset (x, e) ->
      mkstr "%s = %s"
        (var_py x)
        (expr_py e)
      :: []
  | Salloc (x, e1, e2) ->
      mkstr "%s = %s * [%s]"
        (var_py x)
        (expr_py e1)
        (expr_py e2)
      :: []
  | Swrite (x, e1, e2) ->
      mkstr "%s[%s] = %s"
        (var_py x)
        (expr_py e1)
        (expr_py e2)
      :: []
  | Scall (x, f, es) ->
      mkstr "%s = %s(%s)"
        (var_py x)
        (var_py f)
        (es |> List.map expr_py
            |> String.concat ", ")
      :: []
  | Sseq (p1, p2) ->
      stmt_py' p1 @ stmt_py' p2
  | Sifelse (e, p1, Snop) ->
      mkstr "if %s:" (expr_py e)
        :: indent (stmt_py' p1)
  | Sifelse (e, p1, p2) ->
      mkstr "if %s:" (expr_py e)
        :: indent (stmt_py' p1)
      @ "else:"
        :: indent (stmt_py' p2)
  | Swhile (e, p1) ->
      mkstr "while %s:" (expr_py e)
        :: indent (stmt_py' p1)
  | AStmt (st, p1) -> stmt_py' p1

let stmt_py s =
  String.concat "\n" (stmt_py' s)

let func_py' = function
  | Func (name, params, body, ret) ->
      mkstr "def %s(%s):"
        (var_py name)
        (params |> List.map var_py
                |> String.concat ", ")
      :: indent (stmt_py' body)
      @  indent ((mkstr "return %s" (expr_py ret)) :: [])

let func_py f =
  String.concat "\n" (func_py' f)

let prog_py' = function
  | Prog (funcs, body, ret) ->
      List.map func_py funcs
      @ stmt_py' body
      @ mkstr "print %s" (expr_py ret)
      :: []

let implib_py = String.concat "\n"
  [ "import sys"
  ; "import time"
  ; ""
  ; "def print_val(v):"
  ; "  print(v)"
  ; "  return 0"
  ; ""
  ; "def flush():"
  ; "  sys.stdout.flush()"
  ; ""
  ; "def sleep(i):"
  ; "  time.sleep(i / 1000)"
  ; ""
  ; "def read_bool():"
  ; "  s = sys.stdin.readline().rstrip()"
  ; "  if s == \"True\":"
  ; "    return True"
  ; "  else:"
  ; "    return False"
  ; ""
  ; "def read_int():"
  ; "  s = sys.stdin.readline().rstrip()"
  ; "  try:"
  ; "    return int(s)"
  ; "  except:"
  ; "    return 0"
  ; ""
  ; "def read_str():"
  ; "  return sys.stdin.readline().rstrip()"
  ; ""
  ; ""
  ]

let prog_py p =
  p |> prog_py'
    |> String.concat "\n"
    |> (^) implib_py

let run_py p =
  (* prepare imp *)
  let (tmp, toc) = Filename.open_temp_file "IMPTEST" ".py" in
  output_string toc (prog_py p);
  close_out toc;
  (* run imp prog in python, get results *)
  let (ic, oc, ec) = Unix.open_process_full ("python " ^ tmp) [||] in
  !ImpLib.inputs
    |> List.rev
    |> String.concat "\n"
    |> output_string oc;
  close_out oc; (* flush is not sufficient *)
  let res = ic_str ic in
  let err = ic_str ec in
  let ret = Unix.close_process_full (ic, oc, ec) in
  (* clean up and return *)
  let _ = Unix.system ("rm " ^ tmp) in
  (res, err, ret)

let process_status_str = function
  | Unix.WEXITED i -> mkstr "WEXITED %d" i
  | Unix.WSIGNALED i -> mkstr "WSIGNALED %d" i
  | Unix.WSTOPPED i -> mkstr "WSTOPPED %d" i

let result_pretty (res, err, ret) =
  mkstr "stdout:\n%s\n\nstderr:\n%s\n\nstatus:\n%s\n"
    res err (process_status_str ret)

let results_match ir (res, err, ret) =
  match ret with
  | Unix.WEXITED 0 ->
      let ir_str =
        ir |> ImpPretty.result_pretty
           |> (fun x -> x :: !ImpLib.outputs)
           |> List.rev
           |> String.concat "\n"
      in
      ir_str = res
  | Unix.WEXITED 1 ->
      begin match ir with
      | None -> true
      | _ -> false
      end
  | _ -> false
