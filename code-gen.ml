#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string
  val myGen : expr' list -> string
end;;

module Code_Gen : CODE_GEN = struct

  let rec omit_dup lst = 
  match lst with
  | [] -> []
  | hd::rest -> hd::(omit_dup (List.filter (fun element -> not (element = hd)) rest));;

  

  let rec sub_constants constant =
    (match constant with
    |ScmSymbol str -> [ScmString(str); constant]
    |ScmPair (car, cdr) -> (sub_constants ( car))@[car]@(sub_constants ( cdr))@[cdr] @ [ScmPair (car, cdr)]
    |ScmVector (lst) -> (subVector lst) @ [constant]
    | _ -> [constant])

  and subVector lst =
    match lst with 
    |[]->[]
    |hd::rest -> (sub_constants hd) @ (subVector rest)
  

  let offset_in_const_table const cons_table =  string_of_int (fst (List.assoc const cons_table)) ;;

  let offset_in_fvar_table var fvar_table =  string_of_int (List.assoc var fvar_table);;

  let rec vectorSOBs lst cons_table = 
  match lst with 
  | [] -> ""
  | a :: [] -> "const_tbl+"^(string_of_int (fst (List.assoc a cons_table)))
  | a :: b ->  "const_tbl+"^string_of_int (fst (List.assoc a cons_table))^" , "^ (vectorSOBs b cons_table);;

  let rec cct lst offset cons_table = (*takes a list of contants and returns table structure*)
    match lst with 
    |[] -> cons_table
    | hd:: rest -> (match hd with
      | ScmVoid -> cct rest offset cons_table
      | ScmNil -> cct rest offset cons_table
      | ScmBoolean _ -> cct rest offset cons_table
      | ScmChar c -> cct rest (offset+2) (cons_table @ [(hd,(offset,"MAKE_LITERAL_CHAR(" ^ (string_of_int (int_of_char c )) ^ ")"))])
      | ScmString str -> cct rest (offset + 9 + (String.length str)) (cons_table @ [(hd ,( offset, "MAKE_LITERAL_STRING \"" ^ str ^ "\""))])
      | ScmSymbol(str) -> cct rest (offset+9) (cons_table @ [(hd ,( offset, "MAKE_LITERAL_SYMBOL(const_tbl+"^(offset_in_const_table (ScmString str) cons_table)^")"))])
      | ScmNumber(num) ->  (match num with
                            |ScmRational(a,b) -> cct rest (offset+17) (cons_table @ [(hd ,( offset, ";;"^(string_of_int offset)^"\nMAKE_LITERAL_RATIONAL("^(string_of_int a)^ ","^(string_of_int b)^")" ))])
                            |ScmReal(a)-> cct rest (offset+9) (cons_table @ [(hd ,( offset,  "MAKE_LITERAL_FLOAT(" ^ (string_of_float a) ^ ")" ))]) 
                            )
      (*here we need to get the offset of the embeded structures*)
      | ScmVector(lst) ->
         (* Printf.printf "%s" (vectorSOBs lst cons_table) ; *)
      let vecList = (vectorSOBs lst cons_table)in
       cct rest (offset+9 + 8*(List.length lst)) (cons_table @ [(hd ,( offset,"MAKE_LITERAL_VECTOR "^ vecList))])
      | ScmPair(a,b) -> cct rest (offset+17) (cons_table @ [(hd ,( offset, ";;"^(string_of_int offset)^"\nMAKE_LITERAL_PAIR(const_tbl+" ^(string_of_int (fst (List.assoc a cons_table)))^", const_tbl+"^(string_of_int (fst (List.assoc b cons_table)))^")"))])
    );;



  let rec find_fvars ast = (**ast is of type expr' *)
    match ast with 
    | ScmConst' _ -> []
    | ScmVar'(var) | ScmBox'(var) | ScmBoxGet'(var) -> (match var with
                                                      |VarFree v ->[v]
                                                      |_ -> [])
    | ScmBoxSet'(var, expr)| ScmSet'(var,expr)| ScmDef'(var,expr) -> (find_fvars (ScmVar' var))@ (find_fvars expr)

    | ScmIf'(test,dit,dif) -> (find_fvars test)@(find_fvars dit)@(find_fvars dif)

    | ScmSeq'(expr_lst) -> (List.fold_left (fun acc element -> acc @ (find_fvars element)) [] expr_lst )
    | ScmOr'(expr_lst) -> (List.fold_left (fun acc element -> acc @ (find_fvars element)) [] expr_lst )
    | ScmLambdaSimple'(str_lst,body) -> (find_fvars body)
    | ScmLambdaOpt'(str_lst, str_opt, body) -> (find_fvars body)
    | ScmApplic'(expr, expr_lst) -> (find_fvars expr)@ (List.fold_left (fun acc element -> acc @ (find_fvars element)) [] expr_lst)
    | ScmApplicTP'(expr, expr_lst) -> (find_fvars expr)@ (List.fold_left (fun acc element -> acc @ (find_fvars element)) [] expr_lst)
  
  let rec find_consts ast =
    match ast with 
    | ScmConst' constant -> [constant]
    | ScmVar' _  | ScmBox' _ | ScmBoxGet' _ -> []
    | ScmBoxSet'(_, expr) | ScmSet'(_,expr) | ScmDef'(_,expr) -> find_consts expr

    | ScmIf'(test,dit, dif) -> (find_consts test)@(find_consts dit)@(find_consts dif)
    | ScmSeq'(expr_lst) -> (List.fold_right (fun e acc -> acc @ (find_consts e)) expr_lst [] )

    | ScmOr'(expr_lst) -> (List.fold_right (fun e acc -> acc @ (find_consts e)) expr_lst [])
    
    | ScmLambdaSimple'(_ , body) | ScmLambdaOpt'(_,_,body) -> find_consts body
    
    | ScmApplic'(expr , expr_lst) | ScmApplicTP'(expr , expr_lst) 
        -> (find_consts expr)@ (List.fold_right (fun e acc -> acc @ (find_consts e)) expr_lst []);;
  
  (*counter to distinguish labels*)
  let counter = ref 0;;

  let count () =
    ( counter := 1 + !counter ;
      !counter );;

  let idx_labels labels =
        let idx = count() in
        List.map (fun label -> Printf.sprintf "%s%d" label idx) labels;;

  let rec generate_helper consts fvars e env_size =
    match e with
    | ScmConst' c -> "  mov rax, const_tbl +"
    ^(string_of_int (fst (List.assoc c consts)))
    ^ "\n"

    | ScmVar'(VarParam(str,minor)) -> "mov rax, PVAR("^(string_of_int minor)^")\n"
    | ScmSet'(VarParam(_,minor), expr1) -> (generate_helper consts fvars expr1 env_size)^
                                                    "mov qword [rbp + 8 ∗ (4 + "^(string_of_int minor)^")], rax
                                                     mov rax,  SOB_VOID_ADDRESS\n"
    | ScmVar'(VarBound(_, major, minor)) ->  "mov rax, qword [rbp + 8 ∗ 2]
                                              mov rax, qword [rax + 8 ∗ "^(string_of_int major)^"]
                                              mov rax, qword [rax + 8 ∗ "^(string_of_int minor)^"]\n"
    | ScmSet'(VarBound(_, major, minor), expr1) -> (generate_helper consts fvars expr1 env_size)^
                                                            "mov rbx, qword [rbp + 8 ∗ 2]
                                                             mov rbx, qword [rbx + 8 ∗"^(string_of_int major)^"]
                                                             mov qword [rbx + 8 ∗ "^(string_of_int minor)^"], rax
                                                             mov rax,  SOB_VOID_ADDRESS\n"
    | ScmVar'(VarFree(str)) -> "mov rax, qword [fvar_tbl + "^(offset_in_fvar_table str fvars)^"]\n"
    | ScmSet'(VarFree(str), expr1) -> (generate_helper consts fvars expr1 env_size)^ 
                                              "mov qword [fvar_tbl + "^(offset_in_fvar_table str fvars)^"], rax
                                               mov rax, SOB_VOID_ADDRESS\n"
    | ScmSeq'(expr_lst) -> List.fold_left (fun acc expr -> acc ^ (generate_helper consts fvars expr env_size)) "" expr_lst

    | ScmOr'(expr_lst) -> let idxLexit = List.nth  (idx_labels ["Lexit"]) 0 in
      let rec ghOr lst endStr =
        match lst with
        |[] -> endStr
        |hd :: [] -> endStr ^(generate_helper consts fvars hd env_size) ^idxLexit^ ":\n"
        |hd::rest -> ghOr rest (endStr ^ (generate_helper consts fvars hd env_size)^"cmp rax, SOB_FALSE_ADDRESS
        jne "^ idxLexit ^"\n") in
      ghOr expr_lst ""

    | ScmIf'(test,dit,dif) -> let idxLabels = idx_labels ["Lexit";"Lelse"] in
                              let exitl = List.nth idxLabels 0 in
                              let elsel = List.nth idxLabels 1 in
        (generate_helper consts fvars test env_size)^"cmp rax, SOB_FALSE_ADDRESS
        je "^elsel^"\n"^(generate_helper consts fvars dit env_size)^"jmp "^ exitl^"
        "^elsel^":\n"^(generate_helper consts fvars dif env_size)^"\n"^ exitl ^":\n"
    | ScmBoxGet'(v) -> "mov rax, qword [rax]\n"
    | ScmBoxSet'((v), expr) -> (generate_helper consts fvars expr env_size) ^ "push rax\n" ^
                                        (generate_helper consts fvars (ScmVar'(v)) env_size) ^"pop qword [rax]
                                                                                               mov rax, SOB_VOID_ADDRESS\n"
    | ScmLambdaSimple'(str_lst,body) -> 
      let lbls = idx_labels ["Lcode"; "Lcont";] in
      let codel = List.nth lbls 0 in
      let contl = List.nth lbls 1 in
      codel^":
      push rbp
      mov rbp , rsp
      "^(generate_helper consts fvars body (env_size+1))^"
      leave
      ret
      "^contl ^":"
    | ScmApplic'(expr,expr_lst) -> 
      let n = List.length expr_lst in

      let rec applicLoop lst =
        match lst with
        |[] -> (generate_helper consts fvars expr env_size)
        (* ^"Verify that rax has type closure
                push rax→ env
                call rax→ code\n" *)
        |hd::[] -> (generate_helper consts fvars hd env_size)^ "push rax
        push "^(string_of_int n)^"\n"^ (generate_helper consts fvars expr env_size)
        (* ^"Verify that rax has type closure
        push rax→ env
        call rax→ code\n" *)
        |hd::rest -> (generate_helper consts fvars hd env_size)^ "push rax\n" ^(applicLoop rest)  in
      (applicLoop expr_lst) ^ 
      " CLOSURE_ENV rbx, rax      ; rbx = rax -> env
      push rbx
      CLOSURE_CODE rax, rax     ; rax = rax -> code
      call rax                  ; do proc(params)
      ;; and now let's clean the stack
      add rsp, WORD_SIZE * 1    ; pop env
      pop rbx                   ; pop arg count
      shl rbx, 3                ; rbx = rbx * 8
      add rsp, rbx              ; pop args\n"
      

    | ScmDef'(VarFree(str),expr) -> "mov qword[fvar_tbl + WORD_SIZE*"^(string_of_int (List.assoc str fvars))^"] , rax
    mov rax,SOB_VOID_ADDRESS\n"

    | _ -> ""

   
    (* | ScmBox' of var' *)
    
    (* | ScmDef' of var' * expr' *)
    
    (* | ScmLambdaSimple' of string list * expr' *)
    (* | ScmLambdaOpt' of string list * string * expr' *)
    
    (* | ScmApplicTP' of expr' * (expr' list);; *)


  let make_consts_tbl asts =  
    (* [(ScmVoid, (0, "MAKE_VOID")); (ScmNil, (1, "MAKE_NIL")); (ScmBoolean false, (2, "MAKE_BOOL(0)")); (ScmBoolean true, (4, "MAKE_BOOL(1)"))] *)
    (* raise X_not_yet_implemented;; *)
    let basic_const_table = [(ScmVoid, (0, "MAKE_VOID")); (ScmNil, (1, "MAKE_NIL")); (ScmBoolean false, (2, "MAKE_BOOL(0)")); (ScmBoolean true, (4, "MAKE_BOOL(1)"))] in
    let all_consts = (List.fold_right (fun ast acc -> (find_consts ast) @ acc) asts []) in
    let set_consts = (omit_dup all_consts) in
    let extended_consts = (List.fold_right (fun ast acc -> (sub_constants ast) @ acc) set_consts []) in
    let set_extended_consts = (omit_dup extended_consts) in
    cct set_extended_consts 6  basic_const_table 
    (* give an intial consts table and initial offset *)



  let make_fvars_tbl asts = 
    let basic =[
    (* Type queries  *)
    "boolean?"; "flonum?"; "rational?";
    "pair?"; "null?"; "char?"; "string?";
    "procedure?"; "symbol?";
    (* String procedures *)
    "string-length"; "string-ref"; "string-set!";
    "make-string"; "symbol->string";
    (* Type conversions *)
    "char->integer"; "integer->char"; "exact->inexact";
    (* Identity test *)
    "eq?";
    (* Arithmetic ops *)
    "+"; "*"; "/"; "="; "<";
    (* Additional rational numebr ops *)
    "numerator"; "denominator"; "gcd";
    (* you can add yours here *)
    (*stdlib*)
    "fold-left"; "fold-right";"cons*"
  ] in
       (* ["*"; "+" ; "-" ; "/"; "<"; "=";">";
    "append";"apply";  "boolean?"; "car"; "cdr"; "char->integer"; "char?"; "cons"; "cons*"
    ; "denominator"; "eq?"; "equal?"; "exact->inexact"; "flonum?"; "fold-left"; "fold-right"; "gcd"
    ; "integer?";"integer->char"; "length"; "list" ; "list?";"make-string"; "map";"not"; "null?"; "number?";
     "numerator"; "pair?"; "procedure?"; "rational?"; "set-car!"; "set-cdr!";
    "string->list"; "string-length"; "string-ref"; "string-set!"; "string?"; "symbol?"; "symbol->string";"zero?"] *)
   
    (* raise X_not_yet_implemented;; *)
    let all_fvars = basic @ (List.fold_right (fun ast acc -> (find_fvars ast) @ acc) asts []) in
    let fvar_set = (omit_dup all_fvars) in
    List.mapi (fun idx element -> (element,idx)) fvar_set;;

  

  let generate consts fvars e = 
    generate_helper consts fvars e 0 ;;
     (* raise X_not_yet_implemented;; *)

  let myGen e = 
   let fvar = make_fvars_tbl e in
   let myconsts = make_consts_tbl e in
   generate myconsts fvar (List.nth e 0);;
   (* "done" ;; *)
end;;

