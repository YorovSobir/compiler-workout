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
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
open Language.Expr
open Language
let rec eval env ((cstack, stack, ((st, i, o) as stmtConf)) as conf) prog =
    match prog with
        | [] -> conf
        | ins :: insxs -> (
            match ins with
            | BINOP op -> let y :: x :: stack' = stack
                          in eval env (cstack, (binop op x y) :: stack', stmtConf) insxs
            | CONST num -> eval env (cstack, num :: stack, stmtConf) insxs
            | READ -> let z :: ixs = i
                      in eval env (cstack, z :: stack, (st, ixs, o)) insxs
            | WRITE -> let z :: stack' = stack
                       in eval env (cstack, stack', (st, i, o@[z])) insxs
            | LD x -> eval env (cstack, (State.eval st x) :: stack, stmtConf) insxs
            | ST x -> let z :: stack' = stack
                      in eval env (cstack, stack', (State.update x z st, i, o)) insxs
            | LABEL l -> eval env conf insxs
            | JMP l -> eval env conf (env#labeled l)
            | CJMP (cond, l) -> (
                let z :: stack' = stack in
                match cond with
                | "z" when z == 0 -> eval env conf (env#labeled l)
                | "z" when z != 0 -> eval env conf insxs
                | "nz" when z == 0 -> eval env conf insxs
                | "nz" when z != 0 -> eval env conf (env#labeled l)
                | _ -> failwith @@ "unsupported condition " ^ cond
            )
            | BEGIN (params, locals) -> (
                let rec values params stack = fun res -> match params, stack with
                | [], stack' -> res, stack'
                | a :: params', v :: stack' -> values params' stack' ([v] @ res)
                | _, _ -> failwith @@ "not equal length" in
                let vals, stack' = values params stack [] in
                let state = State.enter st (params @ locals) in
                let updateList = List.fold_left2 (fun st' x v -> State.update x v st') in
                let state' = updateList state params vals in
                eval env (cstack, stack', (state', i, o)) insxs
            )
            | END -> (
                let (p', st') :: cstack' = cstack in
                eval env (cstack', stack, (State.leave st st', i, o)) p'
            )
            | CALL funcName -> (
                let cstack' = [(insxs, st)] @ cstack in
                eval env (cstack', stack, stmtConf) (env#labeled funcName)
            )
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

open Language.Stmt

let compile (defs, p) =
    let genLabel n = ("L" ^ (string_of_int n), n + 1) in
    let rec compileExpr exprT =
       match exprT with
       | Const num -> [CONST num]
       | Var x -> [LD x]
       | Binop (op, exprT1, exprT2) -> (compileExpr exprT1) @ (compileExpr exprT2) @ [BINOP op]
    in
    let rec compileStmt stmt n =
        match stmt with
        | Read x -> [READ; ST x], n
        | Write exprT -> (compileExpr exprT) @ [WRITE], n
        | Assign (x, exprT) -> (compileExpr exprT) @ [ST x], n
        | Seq (stmt1, stmt2) -> (
            let insn1, n = compileStmt stmt1 n in
            let insn2, n = compileStmt stmt2 n in
                insn1 @ insn2, n
        )
        | If (exprT, stmt1, stmt2) -> (
            let elseLabel, n = genLabel n in
            let exitLabel, n = genLabel n in
            let thenInsn, n = compileStmt stmt1 n in
            let elseInsn, n = compileStmt stmt2 n in
                (compileExpr (Binop ("!=", exprT, Const 0))) @ [CJMP ("z", elseLabel)] @ thenInsn @ [JMP exitLabel] @
                [LABEL elseLabel] @ elseInsn @ [LABEL exitLabel], n
        )
        | While (exprT, stmt) -> (
            let beginLabel, n = genLabel n in
            let loopLabel, n = genLabel n in
            let loopInsn, n = compileStmt stmt n in
                [JMP beginLabel] @ [LABEL loopLabel] @ loopInsn @ [LABEL beginLabel] @
                (compileExpr (Binop ("!=", exprT, Const 0))) @ [CJMP ("nz", loopLabel)], n
        )
        | Repeat (stmt, exprT) -> (
            let loopLabel, n = genLabel n in
            let loopInsn, n = compileStmt stmt n in
                [LABEL loopLabel] @ loopInsn @ (compileExpr (Binop ("!=", exprT, Const 0))) @
                [CJMP ("z", loopLabel)], n
        )
        | Skip -> [], n
        (*| Call (funcName, exprxs) -> (List.flatten (List.map compileExpr exprxs)) @ [JMP funcName], n*)
        | _ -> failwith @@ "not supported"
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
        let mainProgram, _ = compileStmt p, n in
        defsProgram @ mainProgram
