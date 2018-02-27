open GT
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
type config = int list * Syntax.Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)

let evalHelper conf prog confRes =
    match conf with
        (stack, stmtConf) -> (
            match prog with
                | [] -> confRes
                | ins :: insxs -> (
                    match ins with
                        | BINOP op -> (
                            match stack, stmtConf with
                                | y :: x :: st, (exprSt, ixs, oxs) ->
                                    ((Syntax.Expr.eval exprSt (Syntax.Expr.Binop (op, Syntax.Expr.Const x, Syntax.Expr.Const y))) :: st, stmtConf)
                                | _ -> failwith @@ "not enough args in stack"
                        )
                        | CONST num -> (num :: stack, stmtConf)
                        | READ -> (
                            match stmtConf with
                                | (exprSt, z :: ixs, oxs) -> (z :: stack, (exprSt, ixs, oxs))
                                | _ -> failwith @@ "input int list are empty"
                        )
                        | WRITE -> (
                            match stack, stmtConf with
                                | z :: st, (exprSt, ixs, oxs) -> (st, (exprSt, ixs, oxs@[z]))
                                | _ -> failwith @@ "stack is empty"
                        )
                        | LD x -> (
                            match stmtConf with
                                | (exprSt, ixs, oxs) -> ((exprSt x) :: stack, stmtConf)
                        )
                        | ST x -> (
                            match stack, stmtConf with
                                | z :: st, (exprSt, ixs, oxs) -> (st, (Syntax.Expr.update x z exprSt, ixs, oxs))
                                | _ -> failwith @@ "stack is empty"
                        )
                        | _ -> failwith @@ "temp"
                )

        )

let eval conf prog = evalHelper conf prog ([], conf)

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let compile _ = failwith "Not yet implemented"
