(* X86 codegeneration interface *)

(* The registers: *)
let regs = [|"%ebx"; "%ecx"; "%esi"; "%edi"; "%eax"; "%edx"; "%ebp"; "%esp"|]

(* We can not freely operate with all register; only 3 by now *)
let num_of_regs = Array.length regs - 5

(* We need to know the word size to calculate offsets correctly *)
let word_size = 4

(* We need to distinguish the following operand types: *)
type opnd =
| R of int     (* hard register                    *)
| S of int     (* a position on the hardware stack *)
| M of string  (* a named memory location          *)
| L of int     (* an immediate operand             *)

(* For convenience we define the following synonyms for the registers: *)
let ebx = R 0
let ecx = R 1
let esi = R 2
let edi = R 3
let eax = R 4
let edx = R 5
let ebp = R 6
let esp = R 7

(* Now x86 instruction (we do not need all of them): *)
type instr =
(* copies a value from the first to the second operand  *) | Mov   of opnd * opnd
(* makes a binary operation; note, the first operand    *) | Binop of string * opnd * opnd
(* designates x86 operator, not the source language one *)
(* x86 integer division, see instruction set reference  *) | IDiv  of opnd
(* see instruction set reference                        *) | Cltd
(* sets a value from flags; the first operand is the    *) | Set   of string * string
(* suffix, which determines the value being set, the    *)
(* the second --- (sub)register name                    *)
(* pushes the operand on the hardware stack             *) | Push  of opnd
(* pops from the hardware stack to the operand          *) | Pop   of opnd
(* call a function by a name                            *) | Call  of string
(* returns from a function                              *) | Ret
(* a label in the code                                  *) | Label of string
(* a conditional jump                                   *) | CJmp  of string * string
(* a non-conditional jump                               *) | Jmp   of string
(* directive                                            *) | Meta  of string

(* Instruction printer *)
let show instr =
  let binop = function
  | "+"   -> "addl"
  | "-"   -> "subl"
  | "*"   -> "imull"
  | "&&"  -> "andl"
  | "!!"  -> "orl"
  | "^"   -> "xorl"
  | "cmp" -> "cmpl"
  | _     -> failwith "unknown binary operator"
  in
  let opnd = function
  | R i -> regs.(i)
  | S i -> if i >= 0
           then Printf.sprintf "-%d(%%ebp)" ((i + 1) * word_size)
           else Printf.sprintf "%d(%%ebp)"  (8 + (-i - 1) * word_size)
  | M x -> x
  | L i -> Printf.sprintf "$%d" i
  in
  match instr with
  | Cltd               -> "\tcltd"
  | Set   (suf, s)     -> Printf.sprintf "\tset%s\t%s"     suf s
  | IDiv   s1          -> Printf.sprintf "\tidivl\t%s"     (opnd s1)
  | Binop (op, s1, s2) -> Printf.sprintf "\t%s\t%s,\t%s"   (binop op) (opnd s1) (opnd s2)
  | Mov   (s1, s2)     -> Printf.sprintf "\tmovl\t%s,\t%s" (opnd s1) (opnd s2)
  | Push   s           -> Printf.sprintf "\tpushl\t%s"     (opnd s)
  | Pop    s           -> Printf.sprintf "\tpopl\t%s"      (opnd s)
  | Ret                -> "\tret"
  | Call   p           -> Printf.sprintf "\tcall\t%s" p
  | Label  l           -> Printf.sprintf "%s:\n" l
  | Jmp    l           -> Printf.sprintf "\tjmp\t%s" l
  | CJmp  (s , l)      -> Printf.sprintf "\tj%s\t%s" s l
  | Meta   s           -> Printf.sprintf "%s\n" s

(* Opening stack machine to use instructions without fully qualified names *)
open SM

(* Symbolic stack machine evaluator

     compile : env -> prg -> env * instr list

   Take an environment, a stack machine program, and returns a pair --- the updated environment and the list
   of x86 instructions
*)
let quot_or_rem op =
    match op with
        | "/" -> eax
        | "%" -> edx
        | _ -> failwith @@ "wrong op " ^ op

let set_flags op =
    match op with
        | "==" -> "E"
        | "!=" -> "NE"
        | "<=" -> "LE"
        | "<" -> "L"
        | ">=" -> "GE"
        | ">" -> "G"
        | _ -> failwith @@ "wrong op " ^ op

let is_zero x res = [Binop ("^", eax, eax); Mov (x, edx); Binop ("cmp", L 0, edx);
                     Set (set_flags "!=", "%al"); Mov (eax, res)]

let rec compile env = function
    | [] -> env, []
    | instr :: code ->
        let env', asm' =  match instr with
        | CONST n -> let x, env = env#allocate in env, [Mov (L n, x)]
        | LD var -> (
            let v = env#loc var in
            let x, env = env#allocate in
                match x with
                | S _ -> env, [Mov (v, eax); Mov (eax, x)]
                | _ -> env, [Mov (v, x)]
        )
        | ST var -> (
            let v = env#loc var in
            let env = match v with
            | M _ -> env#global var
            | _ -> env in
            let x, env = env#pop in
                match x with
                | S _ | M _ -> env, [Mov (x, eax); Mov (eax, v)]
                | _ -> env, [Mov (x, v)]
        )
        | BINOP op -> (
            let res, env = env#allocate in
            let t_ebx, env = env#allocate in
            let _, _, env = env#pop2 in
            let x, y, env = env#pop2 in
                match op with
                | "+" | "-" | "*" ->
                    env#push res, [Mov (y, eax); Binop (op, x, eax); Mov (eax, res)]
                | "/" | "%" -> (
                    let env, asm = env#push res, [Mov (y, eax); Cltd] in
                    let env, asm' =
                        match x with
                        | S _ | L _ -> env, [Mov (ebx, t_ebx); Mov (x, ebx); IDiv ebx; Mov (t_ebx, ebx)]
                        | _ -> env, [IDiv x]
                        in
                            env, asm @ asm' @ [Mov (quot_or_rem op, res)]
                )
                | "==" | "!=" | "<=" | "<" | ">=" | ">" ->  env#push res,
                    [Binop ("^", eax, eax); Mov (y, edx); Binop ("cmp", x, edx); Set (set_flags op, "%al"); Mov (eax, res)]
                | "&&" | "!!" -> env#push res,
                                (is_zero y res) @ (is_zero x edx) @ [Binop ("^", eax, eax); Binop (op, res, edx);
                                Set (set_flags "!=", "%al"); Mov (eax, res)]
        )
        | WRITE ->
            let x, env = env#pop in
                env, [Push x; Call "Lwrite"; Pop eax]
        | READ ->
            let x, env = env#allocate in
                env, [Call "Lread"; Mov (eax, x)]
        | LABEL l -> env, [Label l]
        | CJMP (cond, l) -> env, [CJmp (cond, l)]
        | JMP l -> env, [Jmp l]
        | BEGIN (funcName, args, locals) -> (
            let env = env#enter funcName args locals in
            env, [Push ebp; Mov (esp, ebp); Binop ("-", M ("$" ^ env#lsize), esp)]
        )
        | END -> (
            env, [Label env#epilogue; Mov (ebp, esp); Pop ebp; Ret;
            Meta (Printf.sprintf "\t.set\t%s, \t%d" env#lsize (env#allocated * word_size))]
        )
        | RET op -> (
            if op then let r, env = env#pop in env, [Mov (r, eax); Jmp env#epilogue]
            else env, [Jmp env#epilogue]
        )
        | CALL (funcName, argsCount, isFunc) -> (
            let pushr, popr = List.split @@ List.map (fun r -> (Push r, Pop r)) env#live_registers in
            let env, code =
                let rec pushArgs env argsCount =
                if argsCount = 0 then env, []
                else let v, env = env#pop in let env, acc = pushArgs env (argsCount - 1) in env, (Push v) :: acc
                in
                let env, pushs = pushArgs env argsCount
                in
                env, pushr @ pushs @ [Call funcName; Binop ("-", L (argsCount * word_size), esp)] @ (List.rev popr)
            in
                (if isFunc then let v, env = env#allocate in env, code @ [Mov (eax, v)] else env, code)
        )
        | _ -> failwith @@ "not implemented yet"

        in
            let env'', asm'' = compile env' code
            in env'', asm' @ asm''

(* A set of strings *)
module S = Set.Make (String)

(* Environment implementation *)
let init_list (l : int) (f : int -> 'a) : 'a list =
    let rec sequence_map l acc = match l with
    | 0 -> acc
    | _ -> sequence_map (l - 1) ((f (l - 1)) :: acc)
    in
    sequence_map l []

let make_assoc l = List.combine l (init_list (List.length l) (fun x -> x))

class env =
  object (self)
    val globals     = S.empty (* a set of global variables         *)
    val stack_slots = 0       (* maximal number of stack positions *)
    val stack       = []      (* symbolic stack                    *)
    val args        = []      (* function arguments                *)
    val locals      = []      (* function local variables          *)
    val fname       = ""      (* function name                     *)

    (* gets a name for a global variable *)
    method loc x =
      try S (- (List.assoc x args)  -  1)
      with Not_found ->
        try S (List.assoc x locals) with Not_found -> M ("global_" ^ x)

    (* allocates a fresh position on a symbolic stack *)
    method allocate =
      let x, n =
	let rec allocate' = function
	| []                            -> ebx     , 0
	| (S n)::_                      -> S (n+1) , n+1
	| (R n)::_ when n < num_of_regs -> R (n+1) , n+1
    | (M _)::s                      -> allocate' s
	| _                             -> S stack_slots, stack_slots
	in
	allocate' stack
      in
      x, {< stack_slots = max n stack_slots; stack = x::stack >}

    (* pushes an operand to the symbolic stack *)
    method push y = {< stack = y::stack >}

    (* pops one operand from the symbolic stack *)
    method pop = let x::stack' = stack in x, {< stack = stack' >}

    (* pops two operands from the symbolic stack *)
    method pop2 = let x::y::stack' = stack in x, y, {< stack = stack' >}

    (* registers a global variable in the environment *)
    method global x  = {< globals = S.add ("global_" ^ x) globals >}

    (* gets all global variables *)
    method globals = S.elements globals

    (* gets a number of stack positions allocated *)
    method allocated = stack_slots

    (* enters a function *)
    method enter f a l =
      {< stack_slots = List.length l; stack = []; locals = make_assoc l; args = make_assoc a; fname = f >}

    (* returns a label for the epilogue *)
    method epilogue = Printf.sprintf "L%s_epilogue" fname

    (* returns a name for local size meta-symbol *)
    method lsize = Printf.sprintf "L%s_SIZE" fname

    (* returns a list of live registers *)
    method live_registers =
      List.filter (function R _ -> true | _ -> false) stack

  end

(* Generates an assembler text for a program: first compiles the program into
   the stack code, then generates x86 assember code, then prints the assembler file
*)
let genasm (ds, stmt) =
  let stmt = Language.Stmt.Seq (stmt, Language.Stmt.Return (Some (Language.Expr.Const 0))) in
  let env, code =
    compile
      (new env)
      ((LABEL "main") :: (BEGIN ("main", [], [])) :: SM.compile (ds, stmt))
  in
  let data = Meta "\t.data" :: (List.map (fun s -> Meta (s ^ ":\t.int\t0")) env#globals) in
  let asm = Buffer.create 1024 in
  List.iter
    (fun i -> Buffer.add_string asm (Printf.sprintf "%s\n" @@ show i))
    (data @ [Meta "\t.text"; Meta "\t.globl\tmain"] @ code);
  Buffer.contents asm

(* Builds a program: generates the assembler file and compiles it with the gcc toolchain *)
let build prog name =
  let outf = open_out (Printf.sprintf "%s.s" name) in
  Printf.fprintf outf "%s" (genasm prog);
  close_out outf;
  let inc = try Sys.getenv "RC_RUNTIME" with _ -> "../runtime" in
  Sys.command (Printf.sprintf "gcc -m32 -o %s %s/runtime.o %s.s" name inc name)
