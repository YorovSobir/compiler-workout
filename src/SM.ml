open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)
 let rec eval conf prog =
     match conf with
         (stack, stmtConf) -> (
             match prog with
                 | [] -> conf
                 | ins :: insxs -> (
                     match ins with
                         | BINOP op -> (
                             match stack, stmtConf with
                                 | y :: x :: st, (exprSt, ixs, oxs) ->
                                     eval ((Language.Expr.eval exprSt (
                                     Language.Expr.Binop (op, Language.Expr.Const x, Language.Expr.Const y))
                                     ) :: st, stmtConf) insxs
                                 | _ -> failwith @@ "not enough args in stack"
                         )
                         | CONST num -> eval (num :: stack, stmtConf) insxs
                         | READ -> (
                             match stmtConf with
                                 | (exprSt, z :: ixs, oxs) -> eval (z :: stack, (exprSt, ixs, oxs)) insxs
                                 | _ -> failwith @@ "input int list are empty"
                         )
                         | WRITE -> (
                             match stack, stmtConf with
                                 | z :: st, (exprSt, ixs, oxs) -> eval (st, (exprSt, ixs, oxs@[z])) insxs
                                 | _ -> failwith @@ "stack is empty"
                         )
                         | LD x -> (
                             match stmtConf with
                                 | (exprSt, ixs, oxs) -> eval ((exprSt x) :: stack, stmtConf) insxs
                         )
                         | ST x -> (
                             match stack, stmtConf with
                                 | z :: st, (exprSt, ixs, oxs) ->
                                     eval (st, (Language.Expr.update x z exprSt, ixs, oxs)) insxs
                                 | _ -> failwith @@ "stack is empty"
                         )
                 )

 )
(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compileExpr exprT =
   match exprT with
       | Language.Expr.Const num -> [CONST num]
       | Language.Expr.Var x -> [LD x]
       | Language.Expr.Binop (op, exprT1, exprT2) -> (compileExpr exprT1) @ (compileExpr exprT2) @ [BINOP op]

let rec compile stmt =
   match stmt with
       | Language.Stmt.Read x -> [READ; ST x]
       | Language.Stmt.Write exprT -> (compileExpr exprT) @ [WRITE]
       | Language.Stmt.Assign (x, exprT) -> (compileExpr exprT) @ [ST x]
| Language.Stmt.Seq (stmt1, stmt2) -> (compile stmt1) @ (compile stmt2)
