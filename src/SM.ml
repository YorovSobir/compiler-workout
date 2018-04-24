open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL  of string * int * bool
(* returns from a function         *) | RET   of bool with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) prg = match prg with
| [] -> conf
| ins :: insxs -> (
    match ins with
    | BINOP op -> (
        let y :: x :: stack' = stack in
        let r' = Expr.binop op x y in
        eval env (cstack, r' :: stack', c) insxs
    )
    | CONST num -> eval env (cstack, num :: stack, c) insxs
    | READ -> let z :: ixs = i
              in eval env (cstack, z :: stack, (st, ixs, o)) insxs
    | WRITE -> let z :: stack' = stack
               in eval env (cstack, stack', (st, i, o@[z])) insxs
    | LD x -> let r' = State.eval st x in eval env (cstack, r' :: stack, c) insxs
    | ST x -> let z :: stack' = stack
              in eval env (cstack, stack', (State.update x z st, i, o)) insxs
    | LABEL l -> eval env conf insxs
    | JMP l -> eval env conf (env#labeled l)
    | CJMP (cond, l) -> (
        let z :: stack' = stack in
        match cond with
        | "z" when z == 0 -> eval env (cstack, stack', c) (env#labeled l)
        | "z" when z != 0 -> eval env (cstack, stack', c) insxs
        | "nz" when z == 0 -> eval env (cstack, stack', c) insxs
        | "nz" when z != 0 -> eval env (cstack, stack', c) (env#labeled l)
        | _ -> failwith @@ "unsupported condition " ^ cond
    )
    | BEGIN (args, locals) -> (
        let rec values args stack = function res -> match args, stack with
        | [], stack' -> res, stack'
        | a :: args', v :: stack' -> values args' stack' (v::res)
        | _, _ -> failwith @@ "not equal length" in
        let argVals, stack' = values args stack [] in
        let funcState = State.enter st (args @ locals) in
        let updateStateWithList = List.fold_left2 (fun st' x v -> State.update x v st') in
        let funcState' = updateStateWithList funcState args argVals in
        eval env (cstack, stack', (funcState', i, o)) insxs
    )
    | END -> (
        match cstack with
        | (insxs', st') :: cstack' -> eval env (cstack', stack, (State.leave st st', i, o)) insxs'
        | _ -> conf
    )
    | CALL funcName -> eval env ((insxs, st) :: cstack, stack, c) (env#labeled funcName)
    | _ -> failwith @@ "not yet implemented"
)
(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)

let compile (defs, p) =
    let genLabel n = ("L" ^ (string_of_int n), n + 1) in
    let rec compileExpr exprT =
       match exprT with
       | Expr.Const num -> [CONST num]
       | Expr.Var x -> [LD x]
       | Expr.Binop (op, expr1, expr2) -> (compileExpr expr1) @ (compileExpr expr2) @ [BINOP op]
       | Expr.Call (funcName, exprxs) -> (List.flatten (List.map compileExpr exprxs)) @ [CALL funcName]
    in
    let rec compileStmt stmt n =
        match stmt with
        | Stmt.Read x -> [READ; ST x], n
        | Stmt.Write exprT -> (compileExpr exprT) @ [WRITE], n
        | Stmt.Assign (x, exprT) -> (compileExpr exprT) @ [ST x], n
        | Stmt.Seq (stmt1, stmt2) -> (
            let insn1, n = compileStmt stmt1 n in
            let insn2, n = compileStmt stmt2 n in
                insn1 @ insn2, n
        )
        | Stmt.If (exprT, stmt1, stmt2) -> (
            let elseLabel, n = genLabel n in
            let exitLabel, n = genLabel n in
            let thenInsn, n = compileStmt stmt1 n in
            let elseInsn, n = compileStmt stmt2 n in
                (compileExpr (Binop ("!=", exprT, Const 0))) @ [CJMP ("z", elseLabel)] @ thenInsn @ [JMP exitLabel] @
                [LABEL elseLabel] @ elseInsn @ [LABEL exitLabel], n
        )
        | Stmt.While (exprT, stmt) -> (
            let beginLabel, n = genLabel n in
            let loopLabel, n = genLabel n in
            let loopInsn, n = compileStmt stmt n in
                [JMP beginLabel] @ [LABEL loopLabel] @ loopInsn @ [LABEL beginLabel] @
                (compileExpr (Binop ("!=", exprT, Const 0))) @ [CJMP ("nz", loopLabel)], n
        )
        | Stmt.Repeat (stmt, exprT) -> (
            let loopLabel, n = genLabel n in
            let loopInsn, n = compileStmt stmt n in
                [LABEL loopLabel] @ loopInsn @ (compileExpr (Binop ("!=", exprT, Const 0))) @
                [CJMP ("z", loopLabel)], n
        )
        | Stmt.Skip -> [], n
        | Stmt.Call (funcName, exprxs) -> ((List.flatten (List.map compileExpr exprxs)) @ [CALL funcName], n)
        | Stmt.Return exprOp -> (
            match exprOp with
            | Some e -> (compileExpr e) @ [END], n
            | None -> [END], n
        )
        | _ -> failwith @@ "not yet implemented"
    in
    let compileDefs defs =
        let mapper (p, n) (funcName, (params, locals, bodyStmt)) =
            let stmtPrg, n = compileStmt bodyStmt n in
            p @ [LABEL funcName; BEGIN (params, locals)] @ stmtPrg @ [END], n
        in
        let p', n = List.fold_left mapper ([], 1) defs in
        p', n
    in
    let defsProgram, n = compileDefs defs in
    let mainProgram, _ = compileStmt p n in
    mainProgram @ [END] @ defsProgram
