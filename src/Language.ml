(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list with show

    let to_int = function
    | Int n -> n
    | _ -> failwith "int value expected"

    let to_string = function
    | String s -> s
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    let update_array  a i x = List.init   (List.length a)   (fun j -> if j = i then x else List.nth a j)

  end

(* States *)
module State =
  struct

    (* State: global state, local state, scope variables *)
    type t = {g : string -> Value.t; l : string -> Value.t; scope : string list}

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

(* Builtins *)
module Builtin =
  struct

    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | "$elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String s -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array  a -> List.nth a i
                               )
                    )
    | "$length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | "$array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))

  end

(* Simple expressions: syntax and semantics *)
module Expr =
  struct

    (* The type for expressions. Note, in regular OCaml there is no "@type..."
       notation, it came from GT.
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option

    (* Expression evaluator

          val eval : env -> config -> t -> int * config


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
    | Const num -> (st, i, o, Some (Value.of_int num))
    | Var x -> (st, i, o, Some (State.eval st x))
    | Binop (op, e1, e2) -> (
        let (st', i', o', Some a) = eval env conf e1 in
        let (st'', i'', o'', Some b) = eval env (st', i', o', None) e2 in
        (st'', i'', o'', Some (Value.of_int (binop op (Value.to_int a) (Value.to_int b))))
    )
    | Call (funcName, exprxs) -> (
        let (st, i, o, args) = eval_list env conf exprxs in
        env#definition env funcName args (st, i, o, None)
    )
    | Array xs -> let (st, i, o, vs) = eval_list env conf xs in Builtin.eval (st, i, o, None) vs "$array"
    | String s -> (st, i, o, Some (Value.String s))
    | Elem (exprObj, exprIn) -> (
        let (st, i, o, Some index) = eval env conf exprIn in
        let (st, i, o, Some v) = eval env (st, i, o, None) exprObj in
        Builtin.eval (st, i, o, None) [v; index] "$elem"
    )
    | Length expr -> let (st, i, o, Some v) = eval env conf expr in Builtin.eval (st, i, o, None) [v] "$length"
    | Sexp   _ -> failwith @@ "not yet implemented"
    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
             let (_, _, _, Some v) as conf = eval env conf x in
             v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)

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
            secondary
        );
        const: n:DECIMAL {Const n};
        var: x:IDENT {Var x};
        string_: s:STRING {String (String.sub s 1 (String.length s - 2))};
        char_: c:CHAR {Const (Char.code c)};
        array_: "[" vs:!(Util.list0)[parse] "]" {Array vs};
        func: name_:IDENT "(" ps:!(Util.list0)[parse] ")" {Call (name_, ps)};
        primary: const | char_ | string_ | func | var | array_ | -"(" expr -")";
        secondary: b:primary is:(-"[" i:parse -"]" {`e i} | "." %"length" {`l})*
            {List.fold_left (fun b -> function `e i -> Elem(b, i) | `l -> Length b) b is}
    )

  end

(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The
       environment is the same as for expressions
    *)

    let update st x v is =
      let rec update a v = function
      | []    -> v
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          )
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

    let rec eval env ((st, i, o, r) as conf) k stmt =
        let cont s1 s2 = match s2 with
        | Skip -> s1
        | _ -> Seq (s1, s2)
        in
        match stmt with
        | Assign (x, exprIs, exprT) -> (
            let (st, i, o, is) = Expr.eval_list env conf exprIs in
            let (st, i, o, Some v) = Expr.eval env conf exprT in
            eval env (update st x v is, i, o, None) Skip k
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
            match (Value.to_int n) with
            | 0 -> eval env conf' k stmt2
            | _ -> eval env conf' k stmt1
        )
        | While (exprT, stmt) -> (
            let (st', i', o', Some n) = Expr.eval env conf exprT in
            let conf' = (st', i', o', None) in
            match (Value.to_int n) with
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
        other: func | assign | if_ | while_ | for_ | repeat_ | skip | return_;
        func: name_:IDENT "(" ps:!(Util.list0By)[ostap (",")][ostap (!(Expr.parse))] ")" {Call (name_, ps)};
        assign: x:IDENT is:(-"[" !(Expr.parse) -"]")* -":=" expr:!(Expr.parse) {Assign (x, is, expr)};
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
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
