(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* States *)
module State =
  struct

    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let emptyGlobalScope = fun x -> failwith (Printf.sprintf "Undefined variable %s in global" x)
    let emptyLocalScope = fun x -> failwith (Printf.sprintf "Undefined variable %s in locals" x)

    let empty = {g = emptyGlobalScope; l = emptyLocalScope; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x
       to value v and returns the new state w.r.t. a scope
    *)
    let updateInsideScope x v s = fun y -> if x = y then v else s y

    let update x v s = let {g = g_; l = l_; scope = scope_} = s
    in
        match (List.mem x scope_) with
        | true -> {g = g_; l = updateInsideScope x v l_; scope = scope_}
        | _ -> {g = updateInsideScope x v g_; l = l_; scope = scope_}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = let {g = g_; l = l_; scope = scope_} = s
    in
        match (List.mem x scope_) with
        | true -> l_ x
        | false -> g_ x

    (* Creates a new scope, based on a given state *)
    let enter st xs = let {g = g_; l = _; scope = _} = st
    in {g = g_; l = emptyLocalScope; scope = xs}

    (* Drops a scope *)
    let leave curState prevState = let {g = g_; l = _; scope = _ } = curState in
        let {g = _; l = l_; scope = scope_} = prevState in
        {g = g_; l = l_; scope = scope_}

  end

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
        | Var x -> State.eval s x
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
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* call a procedure                 *) | Call   of string * Expr.t list with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters, local variables, and a body for given definition
    *)
    let rec eval env ((st, i, o) as conf) stmt =
    match stmt with
        | Write exprT -> (st, i, o @ [(Expr.eval st exprT)])
        | Read x -> let z :: ixs = i
                    in (State.update x z st, ixs, o)
        | Assign (x, exprT) -> (State.update x (Expr.eval st exprT) st, i, o)
        | Seq (stmt1, stmt2) -> eval env (eval env conf stmt1) stmt2
        | Skip -> conf
        | If (exprT, stmt1, stmt2) -> (
                match (Expr.eval st exprT) with
                | 0 -> eval env conf stmt2
                | _ -> eval env conf stmt1
        )
        | (While (exprT, stmt)) as loop -> (
                match (Expr.eval st exprT) with
                | 0 -> conf
                | _ -> eval env (eval env conf stmt) loop
        )
        | Repeat (stmt, exprT) as loop -> (
            let confRes = eval env conf stmt in
            let (exprSt, ixs, oxs) = confRes in
                match (Expr.eval exprSt exprT) with
                | 0 -> eval env confRes loop
                | _ -> confRes
        )
        | Call (funcName, exprxs) -> (
            let (args, locals, body) = env#definition funcName in
            let updateStateWithList = List.fold_left2 (fun state x v -> State.update x (Expr.eval st v) state) in
            let funcState = updateStateWithList (State.enter st (args @ locals)) args exprxs in
            let (funcState', i', o') = eval env (funcState, i, o) body in
            (State.leave funcState' st, i', o')
        )

    (* Statement parser *)
    ostap (
        parse: seq | other;
        seq: s1:other -";" s2:seq {Seq (s1, s2)} | other;
        other: func | read | write | assign | if_ | while_ | for_ | repeat_ | skip;
        func: name_:IDENT "(" ps:!(Util.list0By)[ostap (",")][ostap (!(Expr.parse))] ")" {Call (name_, ps)};
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

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)
    ostap (
      parse: func;
      func: %"fun" name_:IDENT "(" ps:parameters ")" ls:funcLocals body:funcBody {(name_, (ps, ls, body))};
      parameters: ps:!(Util.list0By)[ostap (",")][ostap (IDENT)] {ps};
      funcLocals: %"local" ls:!(Util.list0By)[ostap (",")][ostap (IDENT)] {ls} | empty {[]};
      funcBody: "{" stmt:!(Stmt.parse) "}" {stmt}
    )
  end

(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
    let module M = Map.Make (String) in
    let rec make_map m = function
    | []              -> m
    | (name, func_) :: tl -> make_map (M.add name func_ m) tl
    in
    let m = make_map M.empty defs in
    let (_, _, o) = Stmt.eval (object method definition d = M.find d m end) (State.empty, i, []) body in o

(* Top-level parser *)
let parse = ostap (
    ds:!(Definition.parse)* m:!(Stmt.parse) {(ds, m)}
)
