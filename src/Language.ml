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
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

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
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option

    (* Expression evaluator

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration,
       an returns a pair: the return value for the call and the resulting configuration
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

    let rec eval env ((st, i, o, r) as conf) expr =
    match expr with
    | Const num -> (st, i, o, Some num)
    | Var x -> (st, i, o, Some (State.eval st x))
    | Binop (op, e1, e2) -> (
        let (st', i', o', Some a) = eval env conf e1 in
        let (st'', i'', o'', Some b) = eval env (st', i', o', None) e2 in
        (st'', i'', o'', Some (binop op a b))
    )
    | Call (funcName, exprxs) -> (
        let foldFunc = fun ((st', i', o', v) as conf', acc) e -> let ((st'', i'', o'', Some v') as conf'') = eval env conf e in (conf'', acc @ [v']) in
        let (conf', argsInt) = List.fold_left foldFunc (conf, []) exprxs in
        env#definition env funcName argsInt conf'
    )

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
    *)
    ostap (
        parse: expr;
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
        func: name_:IDENT "(" ps:!(Util.list0By)[ostap (",")][parse] ")" {Call (name_, ps)};
        primary: func | const | var | -"(" expr -")"
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
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The
       environment is the same as for expressions
    *)
    let rec eval env ((st, i, o, r) as conf) k stmt =
    let cont s1 s2 = match s2 with
    | Skip -> s1
    | _ -> Seq (s1, s2) in
    match stmt with
    | Write exprT -> (
        let (st', i', o', Some n) = Expr.eval env conf exprT in
        eval env (st', i', o' @ [n], None) Skip k
    )
    | Read x -> let z :: ixs = i in eval env (State.update x z st, ixs, o, None) Skip k
    | Assign (x, exprT) -> (
        let (st', i', o', Some n) = Expr.eval env conf exprT in
        eval env (State.update x n st', i', o', None) Skip k
    )
    | Seq (stmt1, stmt2) -> eval env conf (cont stmt2 k) stmt1
    | Skip -> (
        match k with
        | Skip -> conf
        | _ -> eval env conf Skip k
    )
    | If (exprT, stmt1, stmt2) -> (
        let (st', i', o', Some n) = Expr.eval env conf exprT in
        let conf' = (st', i', o', None) in
        match n with
        | 0 -> eval env conf' k stmt2
        | _ -> eval env conf' k stmt1
    )
    | While (exprT, stmt) -> (
        let (st', i', o', Some n) = Expr.eval env conf exprT in
        let conf' = (st', i', o', None) in
        match n with
        | 0 -> eval env conf' Skip k
        | _ -> eval env conf' (cont (While (exprT, stmt)) k) stmt
    )
    | Repeat (stmt, exprT) -> eval env conf (cont (While (Expr.Binop ("==", exprT, Expr.Const 0), stmt)) k) stmt
    | Call (funcName, exprxs) -> (
        let foldFunc = fun ((st', i', o', v) as conf', acc) e -> let ((st'', i'', o'', Some v') as conf'') = Expr.eval env conf e in (conf'', acc @ [v']) in
        let (conf', argsInt) = List.fold_left foldFunc (conf, []) exprxs in
        eval env (env#definition env funcName argsInt conf') Skip k
    )
    | Return exprOp -> (
        match exprOp with
        | Some expr -> Expr.eval env conf expr
        | None -> conf
    )
    | _ -> failwith @@ "unsupported stmt"

    (* Statement parser *)
    ostap (
        parse: seq | other;
        seq: s1:other ";" s2:seq {Seq (s1, s2)} | other;
        other: read | func | write | assign | if_ | while_ | for_ | repeat_ | skip | return_;
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
        skip: %"skip" {Skip};
        return_: %"return" e:(!(Expr.parse))? {Return e}
    )

  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
        arg  : IDENT;
        parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
                locs:(%"local" !(Util.list arg))?
                "{" body:!(Stmt.parse) "}" {
                (name, (args, (match locs with None -> [] | Some l -> l), body))
                }
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
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =
           let xs, locs, s      = snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
