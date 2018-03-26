open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
<<<<<<< HEAD
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)                                                               
=======
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)
>>>>>>> hw4
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

<<<<<<< HEAD
   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env conf prog = failwith "Not yet implemented"
=======
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
>>>>>>> hw4

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
<<<<<<< HEAD
let compile p = failwith "Not yet implemented"
=======
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
>>>>>>> hw4
