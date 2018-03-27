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
(* conditional jump                *) | CJMP  of string * string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
open Language.Expr

let rec eval env conf prog =
    let (stack, stmtConf) = conf in
    match prog with
        | [] -> conf
        | ins :: insxs -> (
            match ins with
            | BINOP op -> (
                match stack, stmtConf with
                | y :: x :: st, (exprSt, ixs, oxs) ->
                     eval env ((Language.Expr.eval exprSt (Binop (op, Const x, Const y))) :: st, stmtConf) insxs
                | _ -> failwith @@ "not enough args in stack"
            )
            | CONST num -> eval env (num :: stack, stmtConf) insxs
            | READ -> (
                match stmtConf with
                | (exprSt, z :: ixs, oxs) -> eval env (z :: stack, (exprSt, ixs, oxs)) insxs
                | _ -> failwith @@ "input int list are empty"
            )
            | WRITE -> (
                match stack, stmtConf with
                | z :: st, (exprSt, ixs, oxs) -> eval env (st, (exprSt, ixs, oxs@[z])) insxs
                | _ -> failwith @@ "stack is empty"
            )
            | LD x -> (
                let (exprSt, ixs, oxs) = stmtConf in
                    eval env ((exprSt x) :: stack, stmtConf) insxs
            )
            | ST x -> (
                match stack, stmtConf with
                | z :: st, (exprSt, ixs, oxs) ->
                     eval env (st, (update x z exprSt, ixs, oxs)) insxs
                | _ -> failwith @@ "stack is empty"
            )
            | LABEL l -> eval env conf insxs
            | JMP l -> eval env conf (env#labeled l)
            | CJMP (cond, l) -> (
                let (z :: st) = stack in
                match cond with
                | "z" when z == 0 -> eval env conf (env#labeled l)
                | "z" when z != 0 -> eval env conf insxs
                | "nz" when z == 0 -> eval env conf insxs
                | "nz" when z != 0 -> eval env conf (env#labeled l)
                | _ -> failwith @@ "unsupported condition " ^ cond
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
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
open Language.Stmt

let rec compileExpr exprT =
   match exprT with
       | Const num -> [CONST num]
       | Var x -> [LD x]
       | Binop (op, exprT1, exprT2) -> (compileExpr exprT1) @ (compileExpr exprT2) @ [BINOP op]

let rec compile stmt =
    let genLabel n = ("L" ^ (string_of_int n), n + 1) in
    let rec compileHelper stmt n =
        match stmt with
           | Read x -> [READ; ST x], n
           | Write exprT -> (compileExpr exprT) @ [WRITE], n
           | Assign (x, exprT) -> (compileExpr exprT) @ [ST x], n
           | Seq (stmt1, stmt2) -> (
                let insn1, n = compileHelper stmt1 n in
                let insn2, n = compileHelper stmt2 n in
                    insn1 @ insn2, n
           )
           | If (exprT, stmt1, stmt2) -> (
                let elseLabel, n = genLabel n in
                let exitLabel, n = genLabel n in
                let thenInsn, n = compileHelper stmt1 n in
                let elseInsn, n = compileHelper stmt2 n in
                    (compileExpr (Binop ("!=", exprT, Const 0))) @ [CJMP ("z", elseLabel)] @ thenInsn @ [JMP exitLabel] @
                    [LABEL elseLabel] @ elseInsn @ [LABEL exitLabel], n
           )
           | While (exprT, stmt) -> (
                let beginLabel, n = genLabel n in
                let loopLabel, n = genLabel n in
                let loopInsn, n = compileHelper stmt n in
                    [JMP beginLabel] @ [LABEL loopLabel] @ loopInsn @ [LABEL beginLabel] @
                    (compileExpr (Binop ("!=", exprT, Const 0))) @ [CJMP ("nz", loopLabel)], n
           )
           | Repeat (stmt, exprT) -> (
                let loopLabel, n = genLabel n in
                let loopInsn, n = compileHelper stmt n in
                    [LABEL loopLabel] @ loopInsn @ (compileExpr (Binop ("!=", exprT, Const 0))) @
                    [CJMP ("z", loopLabel)], n
           )
           | Skip -> [], n
           | _ -> failwith @@ "not supported"
   in
        let insn, _ = compileHelper stmt 0 in
            insn
