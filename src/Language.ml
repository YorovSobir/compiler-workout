(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
open Ostap
(* Simple expressions: syntax and semantics *)
module Expr =
  struct

    (* The type for expressions. Note, in regular OCaml there is no "@type..."
       notation, it came from GT.
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* State: a partial map from variables to integer values. *)
    type state = string -> int

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    (* Expression evaluator

          val eval : state -> t -> int

       Takes a state and an expression, and returns the value of the expression in
       the given state.
     *)
    let int_of_bool b = if b then 1 else 0
    let bool_of_int num = if num <> 0 then true else false
    let binop op x y = match op with
        | "!!" -> int_of_bool @@ ( || ) (bool_of_int x) (bool_of_int y)
        | "&&" -> int_of_bool @@ ( && ) (bool_of_int x) (bool_of_int y)
        | "==" -> int_of_bool @@ ( = ) x y
        | "!=" -> int_of_bool @@ ( <> ) x y
        | "<=" -> int_of_bool @@ ( <= ) x y
        | "<" -> int_of_bool @@ ( < ) x y
        | ">=" -> int_of_bool @@ ( >= ) x y
        | ">" -> int_of_bool @@ ( > ) x y
        | "+" -> ( + ) x y
        | "-" -> ( - ) x y
        | "*" -> ( * ) x y
        | "/" -> ( / ) x y
        | "%" -> ( mod ) x y
        | _ -> failwith @@ "unsupported op type " ^ op

    let rec eval s e =
        match e with
        | Const num -> num
        | Var x -> s x
        | Binop (op, e1, e2) -> binop op (eval s e1) (eval s e2)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string

    *)
    ostap (
        parse: expr | const | var;
        expr:
        !(Util.expr
            (fun x -> x)
            [|
                `Lefta, [ostap ("!!"), (fun x y -> Binop ("!!", x, y))];
                `Lefta, [ostap ("&&"), (fun x y -> Binop ("&&", x, y))];
                `Nona, [
                            ostap ("<="), (fun x y -> Binop ("<=", x, y));
                            ostap (">="), (fun x y -> Binop (">=", x, y));
                            ostap ("=="), (fun x y -> Binop ("==", x, y));
                            ostap ("!="), (fun x y -> Binop ("!=", x, y));
                            ostap ("<"), (fun x y -> Binop ("<", x, y));
                            ostap (">"), (fun x y -> Binop (">", x, y));
                       ];
                `Lefta, [
                            ostap ("+"), (fun x y -> Binop ("+", x, y));
                            ostap ("-"), (fun x y -> Binop ("-", x, y));
                        ];
                `Lefta, [
                            ostap ("*"), (fun x y -> Binop ("*", x, y));
                            ostap ("/"), (fun x y -> Binop ("/", x, y));
                            ostap ("%"), (fun x y -> Binop ("%", x, y));
                        ];
            |]
            primary
        );
        const: n:DECIMAL {Const n};
        var: x:IDENT {Var x};
        primary: const | var | -"(" expr -")"
    )

  end

(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t  with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval conf stmt =
        match stmt with
            | Read x -> let (exprSt, z :: ixs, oxs) = conf
                        in (Expr.update x z exprSt, ixs, oxs)
            | Write exprT -> let (exprSt, ixs, oxs) = conf
                             in (exprSt, ixs, oxs@[(Expr.eval exprSt exprT)])
            | Assign (x, exprT) -> let (exprSt, ixs, oxs) = conf
                                   in (Expr.update x (Expr.eval exprSt exprT) exprSt, ixs, oxs)
            | Seq (stmt1, stmt2) -> eval (eval conf stmt1) stmt2
            | Skip -> conf
            | If (exprT, stmt1, stmt2) -> (
                let (exprSt, ixs, oxs) = conf in
                    match (Expr.eval exprSt exprT) with
                    | 0 -> eval conf stmt2
                    | _ -> eval conf stmt1
            )
            | While (exprT, stmt) as loop -> (
                let (exprSt, ixs, oxs) = conf in
                    match (Expr.eval exprSt exprT) with
                    | 0 -> conf
                    | _ -> eval (eval conf stmt) loop
            )
            | Repeat (stmt, exprT) as loop -> (
                let confRes = eval conf stmt in
                let (exprSt, ixs, oxs) = confRes in
                    match (Expr.eval exprSt exprT) with
                    | 0 -> eval confRes loop
                    | _ -> confRes
            )


    (* Statement parser *)
    ostap (
        parse: seq | other;
        seq: s1:other -";" s2:seq {Seq (s1, s2)} | other;
        other: read | write | assign | if_ | while_ | for_ | repeat_ | skip;
        read: %"read" -"(" x:IDENT -")" {Read x};
        write: %"write" -"(" expr:!(Expr.parse) -")" {Write (expr)};
        assign: x:IDENT -":=" expr:!(Expr.parse) {Assign (x, expr)};
        if_: %"if" expr:!(Expr.parse) %"then" stmt:parse %"fi" {If (expr, stmt, Skip)} |
             %"if" expr:!(Expr.parse) %"then" stmt1:parse else_elif:else_or_elif %"fi" {If (expr, stmt1, else_elif)};
        else_or_elif: else_ | elif_;
        else_: %"else" stmt:parse {stmt};
        elif_: %"elif" expr:!(Expr.parse) %"then" stmt:parse rep:else_or_elif {If (expr, stmt, rep)};
        while_: %"while" expr:!(Expr.parse) %"do" stmt:parse %"od" {While (expr, stmt)};
        for_: %"for" init:parse "," expr:!(Expr.parse) "," next:parse %"do" stmt:parse %"od"
                {Seq (init, While (expr, Seq(stmt, next)))};
        repeat_: %"repeat" stmt:parse %"until" expr:!(Expr.parse) {Repeat (stmt, expr)};
        skip: %"skip" {Skip}
    )

  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse
