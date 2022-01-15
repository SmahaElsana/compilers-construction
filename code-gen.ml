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
(**ADD THE SUB PARTS OF THE VECTOR SOBS TO THE CONST TABLE *)
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
      | ScmPair(a,b) ->
         cct rest (offset+17) 
         (cons_table @ [(hd ,( offset, ";;"^(string_of_int offset)^
         "\nMAKE_LITERAL_PAIR(const_tbl+" ^(string_of_int (fst (List.assoc a cons_table)))^", const_tbl+"^(string_of_int (fst (List.assoc b cons_table)))^")"))])
    );;


  (**IN THIS FUNCTION WE ITERATE OVER THE LIST OF EXPR' AND RETURN A LIST OF ALL THE FREE VARS THAT APPEARED *)
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
  
  
    (**USING THIS FUNCTION WE ITERATE OVER THE LIST OF EXPR' AND RETURN A LIST OF ALL CONSTANTS IN IT *)
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
(**THIS FUNCTION USES THE ABOVE COUNTER IN ORDER TO ENUMERATE THE LABELS WHEN HANDLING EACH SEXPR *)
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
                                                    "mov qword[rbp+WORD_SIZE *(4+"^(string_of_int minor)^")] ,rax
                                                    mov rax, SOB_VOID_ADDRESS\n"
                                                    
    | ScmVar'(VarBound(_, major, minor)) -> "
    mov rax ,qword[rbp + WORD_SIZE*2]
    mov rax ,qword[rax + WORD_SIZE*"^(string_of_int major)^"]
    mov rax, qword[rax + WORD_SIZE*"^(string_of_int minor)^"]\n"
      
    | ScmSet'(VarBound(_, major, minor), expr1) -> (generate_helper consts fvars expr1 env_size)^
    "mov rbx, qword[rbp+WORD_SIZE*2]
    mov rbx, qword[rbx+WORD_SIZE*"^(string_of_int major)^"]
    mov qword[rbx+WORD_SIZE*"^(string_of_int minor)^"],rax
    mov rax,SOB_VOID_ADDRESS\n"
    (**COPYING THE ABOVE CODE FROM SLIDES GIVES AN ERROR FOR THE SQUARE BRACETS *)
                                                            (* "mov rbx, qword [rbp + 8 ∗ 2]
                                                             mov rbx, qword [rbx + 8 ∗"^(string_of_int major)^"]
                                                             mov qword [rbx + 8 ∗ "^(string_of_int minor)^"], rax
                                                             mov rax,  SOB_VOID_ADDRESS\n" *)
    | ScmVar'(VarFree(str)) -> "mov rax, qword [fvar_tbl + WORD_SIZE*"^(offset_in_fvar_table str fvars)^"]\n"
    | ScmSet'(VarFree(str), expr1) -> (generate_helper consts fvars expr1 env_size)^ 
                                              "mov qword [fvar_tbl + WORD_SIZE*"^(offset_in_fvar_table str fvars)^"], rax
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
                              ";;IF HEEEEEEERE \n"^
        (generate_helper consts fvars test env_size)^"cmp rax, SOB_FALSE_ADDRESS
        je "^elsel^"\n"^(generate_helper consts fvars dit env_size)^"jmp "^ exitl^"
        "^elsel^":\n"^(generate_helper consts fvars dif env_size)^"\n"^ exitl ^":\n"

    | ScmBoxGet'(v) -> (generate_helper consts fvars (ScmVar'(v)) env_size)^"\nmov rax, qword [rax]\n"
    | ScmBoxSet'((v), expr) -> (generate_helper consts fvars expr env_size) ^ "push rax\n" ^
                                        (generate_helper consts fvars (ScmVar'(v)) env_size) ^"pop qword [rax]
                                                                                               mov rax, SOB_VOID_ADDRESS\n"
    | ScmApplic'(expr,expr_lst) -> 
        (* let rec applicPrms lst =
          (match lst with 
          |[] -> "\n"
          |hd::rest -> (generate_helper consts fvars hd env_size)^ "\npush rax\n" ^ (applicPrms)) in *)
        
        (* let n = (List.length expr_lst) in                                        *)
        let rec applicLoop lst =
        match lst with
        |[] -> ""
        |hd::rest -> (generate_helper consts fvars hd env_size)^ "\npush rax\n" ^(applicLoop rest)   in

      ";; APPLIC IS HINAAAA \n"^
      (applicLoop (List.rev expr_lst))
      (*  THIS IS ANOTHER FOR OPTION (List.fold_left (fun acc param -> (generate_helper consts fvars param env_size) ^ "push rax\n" ^ acc) "" expr_lst) *)
      ^ "\npush "^(string_of_int (List.length expr_lst))^"\n"^(generate_helper consts fvars expr env_size)^
      "\n 
      CLOSURE_ENV rbx, rax \n
      ;; RBX HOLDS THE ADDRESS OF THE ENV OF THE CLOSURE POINTED TO BY RAX REGITER \n\n     
      push rbx\n
      ;; WE PUSH THE RBX SO THAT WE DONT OVERRIDE THE RBX REGISTER THAT POINTS TO THE CLOSURE ENV\n\n\t\n
      CLOSURE_CODE rdx, rax     
      ;; RDX POINTS TO THE CODE OF THE CURRENT CLOSURE\n\n
      call rdx \n
    ;; NOW WE CALLED THE BODY OF THE CLOSURE   \n\t\n              
      ;; TAKE CARE OF THE STACK --> clean the stack
      add rsp, WORD_SIZE * 1    
      pop rbx                  
      shl rbx, 3               
      add rsp, rbx \n\t\n"
      

    | ScmDef'(VarFree(str),expr) -> 
    (generate_helper consts fvars expr env_size)^"mov qword[fvar_tbl + WORD_SIZE*"^(string_of_int (List.assoc str fvars))^"] , rax
    mov rax,SOB_VOID_ADDRESS\n"

    | ScmLambdaSimple'(str_lst ,body) -> 
      let lbls = idx_labels ["lambdaEnv";"lambdaEnvEnd";"lCopyParams";"lCopyParamsEnd";"Lcode"; "Lcont"] in
      let lambdaEnv = (List.nth lbls 0 ) in
      let lambdaEnvEnd = (List.nth lbls 1) in
      let lCopyParams = (List.nth lbls 2) in
      let lCopyParamsEnd = (List.nth lbls 3) in
      let lcode = (List.nth lbls 4) in
      let lcont = (List.nth lbls 5) in
     ( match env_size with
      |0 -> 
    ";; THE INITIAL ENVIRONMENT IS EMPTY SO THERE IS NOTHING TO COPY
    mov rdx, SOB_NIL_ADDRESS
    ;;NOW WE TRY TO COPY PARAMS IF EXIST
    mov rcx,qword[rbp + 3 * WORD_SIZE] ;;rcx holds the number of params
    cmp rcx, 0
    je "^lCopyParamsEnd^" ;;---> NO PARAMS TO COPY JUMP TO END

    mov rax, qword[rbp + 3 * WORD_SIZE]
    shl rax, 3
  ;;NOW RAX HOLDS THE NUMBER OF BYTES WE WANT TO ALLOCATE
  "^
"
    MALLOC rax, rax
;;MALLOC rax, WORD_SIZE * rcx ;;rax holds the address of the newly allocated array for params in extenv
    mov qword[rdx], rax

  "^lCopyParams^":
    mov r10, PVAR(rcx - 1) 
    mov [rax+ 8*(rcx-1)], r10
    dec rcx
    cmp rcx,0
    jne "^lCopyParams^"

    
    "^lCopyParamsEnd^":
    MAKE_CLOSURE(rax, rdx, "^lcode^")

    jmp "^lcont^"\n"
  ^lcode^":

    push rbp
    mov rbp , rsp
    "^ (generate_helper consts fvars body (env_size+1))^"
    leave
    ret
  "^lcont^":\n"

  |_ ->

      ";;LAMBDA IS HIIINA\n

      mov rcx,"^((string_of_int env_size)) ^"
      MALLOC rdx , WORD_SIZE * "^(string_of_int (env_size+1))^" ;;rdx points to extended env
      mov rbx, qword[rbp + WORD_SIZE*2] 
    ;;point to lex env

    "^lambdaEnv^":
      mov r10, qword[rbx + WORD_SIZE*(rcx-1)]
      mov qword[rdx + WORD_SIZE*rcx], r10
      dec rcx
      cmp rcx, 0
      jne "^lambdaEnv^" 

    "^lambdaEnvEnd^":

    ;;NOW WE TRY TO COPY PARAMS IF EXIST
      mov rcx,qword[rbp + 3 * WORD_SIZE] ;;rcx holds the number of params
      cmp rcx, 0
      je "^lCopyParamsEnd^" 

      mov rax, qword[rbp + 3 * WORD_SIZE]
      shl rax, 3

      MALLOC rax, rax
  ;;MALLOC rax, WORD_SIZE * rcx ;;rax holds the address of the newly allocated array for params in extenv
      mov qword[rdx], rax

    "^lCopyParams^":

      mov r10, PVAR(rcx - 1) 
      mov [rax+ 8*(rcx-1)], r10
      dec rcx
      cmp rcx,0
      jne "^lCopyParams^"

      
      "^lCopyParamsEnd^":
      MAKE_CLOSURE(rax, rdx, "^lcode^")

      jmp "^lcont^"\n"
    ^lcode^":

      push rbp
      mov rbp , rsp
      "^ (generate_helper consts fvars body (env_size+1))^"
      leave
      ret
    "^lcont^":\n"
     )


    | ScmBox'(var) ->
      (* "MALLOC rdx, WORD_SIZE\n" ^ *)
                  (generate_helper consts fvars (ScmVar' var) env_size) ^ (**return value of generate_helper is saved in rax*)
                  "MALLOC rdx, WORD_SIZE
                  mov qword [rdx], rax
                  ;;RAX HOLDS THA RETURNED VALUE OF THE GENERATE_HELPER FUNCTION
                  ;;RDX HOLDS THE ADDRESS OF SPACE ALLOCATED
                   mov rax, rdx\n"

    | ScmLambdaOpt'(str_lst, str_opt, expr) ->
      let lbls = idx_labels ["lambdaEnv";"lambdaEnvEnd";"lCopyParams";"lCopyParamsEnd";"Lcode"; "Lcont";"Lequals";"shiftdown";"shrinkstack";"doneadjust";"createList";"addParams2lst";"createClosure";"copyEnv";"shiftup"] in
      (* let lambdaEnv = (List.nth lbls 0 ) in *)
      (* let lambdaEnvEnd = (List.nth lbls 1) in *)
      (* let lCopyParams = (List.nth lbls 2) in *)
      (* let lCopyParamsEnd = (List.nth lbls 3) in *)
      let lcode = (List.nth lbls 4) in
      let lcont = (List.nth lbls 5) in
      (* let lequals = (List.nth lbls 6) in *)
      let lsdown = (List.nth lbls 7) in
      let shrinkstack = (List.nth lbls 8) in
      let doneadjust = (List.nth lbls 9) in
      let createList = (List.nth lbls 10) in
      let addPrms2lst = (List.nth lbls 11) in
      let createClo = (List.nth lbls 12) in
      let copyEnv = (List.nth lbls 13) in
      let shiftup = (List.nth lbls 14) in

      (match env_size with
      |0 ->
        (";;LAMBDA OPT IS HINNA
        mov rdx, SOB_NIL_ADDRESS
        mov rcx, " ^ (string_of_int env_size) ^ " 
        cmp rcx, 0\n\n\n"^
    
      createClo^":\n\n
    
      MAKE_CLOSURE (rax, rdx,  "^lcode^" )
        jmp "^lcont^" \n" ^
      
      lcode^":\n
      
        ;;ADJUST STACK HERE****************************************************************
        mov r15, qword [rsp + WORD_SIZE * 2]                    
        ;; r15 = the number of arguments on the stack sum of opt and non opt args
        mov r14, " ^ (string_of_int (List.length str_lst)) ^ "   
        ;; r14 = |str_lst| the number of non opt params
        cmp r15, r14
        ;; IF THE |OPT ARGS|=0 THEN R14=R15 --> NO NEED TO SHRINK THE STACK --> SHIFT THE SACK & CREATE EMPTY LIST
        jne  "^shrinkstack^"\n"^ 
    
        "sub rsp, WORD_SIZE  
        \t ;; Create space for the params list BY shiftING THE stack\n\t\n"^
    
        "mov rcx, 0  
      mov rdx, " ^ (string_of_int ((List.length str_lst)+3)) ^ " \n      
        ;; RDX HOLDS THE FOLLOWING |arg| + WORD(holds #args)+ WORD(holds lex-env) + WORD(holds ret-addr)
      \n" ^
        "\t\n;;HERE WE SHIFT DOWN THE STACK SINCE THE MANDATORY ARGS EQUAL THE NUMBER OF ARGS ON THE STACK\t\n"^
        ";; THE NUMBER OF OPT ARGS HERE IS 0 --> WE CREATE AN EMPTY LIST AND ADD IT TO THE STACK\t\n\n"^
    
      lsdown^" :
      ;;HERE WE SHIFT DOWN THE STACK IN ORDER TO CREATE SPACE FOR THE OPT LIST
        mov r8, [rsp + WORD_SIZE * (rcx + 1)]
        mov [rsp + WORD_SIZE * rcx], r8
        inc rcx
    
    cmp rcx, rdx
        ;;MOVING TO THE NEXT WORD ON THE STACK --->PARAMS/ LEX / RET-ADDRESS / #ARGS
        jne "^lsdown^
        
        
        "\n\n mov qword [rsp + WORD_SIZE * rcx], SOB_NIL_ADDRESS \n  
      ;; NOW WE add the empty list
    
      inc r14
      mov [rsp + WORD_SIZE * 2], r14
      jmp "^doneadjust^"
      
    ;;SHRINK STACK -> THERE ARE OPT ARGS\n" ^
    
      "\n\n\t ;;WE SHRINK THE STACK #OPTARGS-1 BECUASE WE TAKE THE OPT ARGS AND PUT THEM IN A LIST AND PUT THE LIST ON TOP \n\t\n"^
      shrinkstack^":
    ;; R15 --> THE NUMBER OF ARGS ON THE STACK --> OPT + NON-OPT
    ;; R14 --> STR-LST THE NUMBER OF MANDATORY(NON OPT) ARGUMENTS
      
    mov rdx, r15 \n                
    sub rdx, r14 \n
    mov rcx, rdx  \n\t\n               
      ;; RCX NOW CONTAINS THE NUMBER OF OPT-ARGS
    
    
      mov r9, SOB_NIL_ADDRESS       
    ;; r9 point to an empty list\n" ^
      ";;MAKE THE LAST CDR OF THE LIST NIL \n\t\n"^
        createList^":
      ;;RCX HOLDS COUNTER\t\n\n
      mov r11, r14
        add r11, rcx                  
        mov r8, [rsp + WORD_SIZE * (2 + r11)]
        MAKE_PAIR(rax, r8, r9)
      ;;AT THIS POINT RAX HOLDS A POINTER TO THE CREATED PAIR
        mov r9, rax
      ;;WE MOVE RAX TO R9 IN ORDER TO CONTINUE RECURSIVLY
        dec rcx
        cmp rcx, 0
        jne "^createList^"
      
    
        
      ;;SHRINK THE STACK HERE
      mov rax, 2
      add rax, r15          
      ;;R15 --> THE NUMBER OF ARGS ON THE STACK --> OPT + NON-OPT ---> RAX = THE NUMBER OF ARGS ON THE STACK               
      
      
      mov qword [rsp + WORD_SIZE * rax], r9   
      ;;NOW THE TOP OF THE FRAME POINTS TO THE OPT ARGS LIST
    
      mov rcx, rax
      dec rcx
      mov r11, r14     
      ;;R14 HOLDS THE #MANDATORY PARAMS --> R11 HOLDS THE #MANDATORY PARAMS 
      add r11, 2       
      ;;ALSO SHIFT THE RETURN ADDRESS AND LEXENV AND THE ARGS COUNT \n\t\n" ^
      
     shiftup^":\n\t\n
      ;;WE SHIFT UP THE STACK IN ORDER TO REMOVE THE THE OPT ARGS FROM THE STACK AND ADD THEM AS A LIST 
      mov r8, qword [rsp + WORD_SIZE * r11]
      mov [rsp + WORD_SIZE * rcx], r8
      ;;SINCE WE CANT MOVE FROM ONE MEMORY ADDRESS TO ANOTHER MEMORY ADDRESS, WE MUST USE AN AUXILARY REGISTER
      dec rcx
      dec r11
      ;;DECREMENT BOTH POINTERS, WHERE WE READ FROM AND WHERE WE WRITE TO 
      cmp r11, 0
      jge  "^shiftup^"\n\t\n 
    
    
    
    ;;RDX HOLDS THE NUMBER OF OPT ARGUMENTS
    dec rdx
    ;;RDX IS DECREMENTED CUZ WE WANT DONT WANT TO REMOVE THE LIST WE ADDED
    shl rdx, 3
      ;; MUL BY 8 = SHIFT 3, TO GET THE NUMBER OF BYTES IN ORDER TO ADD TO RSP POINTER
    
    
      add rsp, rdx   
    ;; NOW WE FIX THE STACK POINTER 
    ;; NOW THE STACK CONTAINS THE OPT-ARGS AS A LIST
      mov qword [rsp + WORD_SIZE * 2], " ^ (string_of_int ((List.length str_lst) + 1)) ^ 
    
      "\t\n ;;NUMBER OF ARGUMENTS ON THE STACK IS UPDATED BECAUSE OF THE OPT ARG
    
    ;;DONE SHRINKING STACK & ADJUST *********************************************************\n" ^
        
      doneadjust^":\n
    ;;AT THIS POINT WE FINISHED ADJUSTING THE STACK ACCORDING TO THE OPT PARAMS\t\n\t\n
        push rbp\n
        mov rbp, rsp\n" ^
        (generate_helper consts fvars expr (env_size+1)) ^ "\n
        leave\n
        ret\n" ^
        lcont^":\n\t\n")
      |_ ->
        (";;LAMBDA OPT IS HINNA
      mov rdx, SOB_NIL_ADDRESS
      mov rcx, " ^ (string_of_int env_size) ^ " 
      cmp rcx, 0
      je "^createClo^"
    ;;create space to store the extended enviorment
  
      MALLOC rdx, WORD_SIZE *" ^ (string_of_int (env_size + 1)) ^ " 
  ;;RDX HOLDS THE ADDRESS OF EXT ENV
    
                                          
    mov r10,qword [rbp+2*WORD_SIZE] 
;;THE ABOVE LINE IS SAME IS PVAR WITH -2
  
    "^copyEnv^":         
  mov r8, qword [r10 + WORD_SIZE * (rcx - 1)] 
  mov qword [rdx + WORD_SIZE * rcx], r8              
      cmp rcx,0
      jnz "^copyEnv^" \n
    
  
  mov r10, PVAR(-1)                
;; PVAR(-1) is the #arguments
  cmp r10,0
  je "^createClo^"
  
  
  ;;create a list where we will store the params
  shl r10, 3                    
  MALLOC r10, r10              
  ;;connect  the list to the extended environment
  mov qword [rdx], r10
  
    
    mov rcx, PVAR(-1)                 
  ;; PVAR(-1) is the #arguments
  
   " ^
    
      addPrms2lst^":
      mov r8, PVAR(rcx - 1) 
      ;;RCX IS OOUR INDEX OF THE ITH PARAM ON THE STACK WE ARE CURRENTLY COPYING \n\t\n                
      mov [r10 + WORD_SIZE * (rcx - 1)], r8
      dec rcx
      cmp rcx, 0
      jnz "^addPrms2lst^"\n\n"^
     
    
    createClo^":\n\n
    ;; NOW WE CREATE THE CLOSURE WITH THE RDX AS A POINTER TO EXT-ENV AND THE LCODE LABEL-> START OF CODE\n\t\n
    MAKE_CLOSURE (rax, rdx,  "^lcode^" )
      jmp "^lcont^" \n\n" ^
    
    lcode^":\n
    
      ;;ADJUST STACK HERE****************************************************************
      mov r15, qword [rsp + WORD_SIZE * 2]                    
      ;; r15 = the number of arguments on the stack sum of opt and non opt args
      mov r14, " ^ (string_of_int (List.length str_lst)) ^ "   
      ;; r14 = |str_lst| the number of non opt params
      cmp r15, r14
      ;; IF THE |OPT ARGS|=0 THEN R14=R15 --> NO NEED TO SHRINK THE STACK --> SHIFT THE SACK & CREATE EMPTY LIST
      jne  "^shrinkstack^"\n"^ 
  
      "sub rsp, WORD_SIZE  
      \t ;; Create space for the params list BY shiftING THE stack\n\t\n"^
  
      "mov rcx, 0  
    mov rdx, " ^ (string_of_int ((List.length str_lst)+3)) ^ " \n      
      ;; RDX HOLDS THE FOLLOWING |arg| + WORD(holds #args)+ WORD(holds lex-env) + WORD(holds ret-addr)
    \n" ^
      "\t\n;;HERE WE SHIFT DOWN THE STACK SINCE THE MANDATORY ARGS EQUAL THE NUMBER OF ARGS ON THE STACK\t\n"^
      ";; THE NUMBER OF OPT ARGS HERE IS 0 --> WE CREATE AN EMPTY LIST AND ADD IT TO THE STACK\t\n\n"^
  
    lsdown^" :
    ;;HERE WE SHIFT DOWN THE STACK IN ORDER TO CREATE SPACE FOR THE OPT LIST
      mov r8, [rsp + WORD_SIZE * (rcx + 1)]
      mov [rsp + WORD_SIZE * rcx], r8
      inc rcx
  
  cmp rcx, rdx
      ;;MOVING TO THE NEXT WORD ON THE STACK --->PARAMS/ LEX / RET-ADDRESS / #ARGS
      jne "^lsdown^
      
      
      "\n\n mov qword [rsp + WORD_SIZE * rcx], SOB_NIL_ADDRESS \n  
    ;; NOW WE add the empty list
  
    inc r14
    mov [rsp + WORD_SIZE * 2], r14
    jmp "^doneadjust^"
    
  ;;SHRINK STACK -> THERE ARE OPT ARGS\n" ^
  
    "\n\n\t ;;WE SHRINK THE STACK #OPTARGS-1 BECUASE WE TAKE THE OPT ARGS AND PUT THEM IN A LIST AND PUT THE LIST ON TOP \n\t\n"^
    shrinkstack^":
  ;; R15 --> THE NUMBER OF ARGS ON THE STACK --> OPT + NON-OPT
  ;; R14 --> STR-LST THE NUMBER OF MANDATORY(NON OPT) ARGUMENTS
    
  mov rdx, r15 \n                
  sub rdx, r14 \n
  mov rcx, rdx  \n\t\n               
    ;; RCX NOW CONTAINS THE NUMBER OF OPT-ARGS
  
  
    mov r9, SOB_NIL_ADDRESS       
  ;; r9 point to an empty list\n" ^
    ";;MAKE THE LAST CDR OF THE LIST NIL \n\t\n"^
      createList^":
    ;;RCX HOLDS COUNTER\t\n\n
    mov r11, r14
      add r11, rcx                  
  ;; R11 HOLDS THE NUMBER OF ARGS ON THE STACK
      mov r8, [rsp + WORD_SIZE * (2 + r11)]
      MAKE_PAIR(rax, r8, r9)
      ;;RAX HOOLDS THE POINTER TO THE NEWLY CREATED PAIR
      mov r9, rax
    ;;WE MOVE RAX TO R9 IN ORDER TO CONTINUE RECURSIVLY
      dec rcx
      cmp rcx, 0
      jne "^createList^"
    
  
      
    ;;SHRINK THE STACK HERE
    mov rax, 2
    add rax, r15          
    ;;R15 --> THE NUMBER OF ARGS ON THE STACK --> OPT + NON-OPT ---> RAX = THE NUMBER OF ARGS ON THE STACK               
    
    
    mov qword [rsp + WORD_SIZE * rax], r9   
    ;;NOW THE TOP OF THE FRAME POINTS TO THE OPT ARGS LIST
  
    mov rcx, rax
    dec rcx
    mov r11, r14     
    ;;R14 HOLDS THE #MANDATORY PARAMS --> R11 HOLDS THE #MANDATORY PARAMS 
    add r11, 2       
    ;;ALSO SHIFT THE RETURN ADDRESS AND LEXENV AND THE ARGS COUNT \n\t\n" ^
    
   shiftup^":\n\t\n
    ;;WE SHIFT UP THE STACK IN ORDER TO REMOVE THE THE OPT ARGS FROM THE STACK AND ADD THEM AS A LIST 
    mov r8, qword [rsp + WORD_SIZE * r11]
    mov [rsp + WORD_SIZE * rcx], r8
    ;;SINCE WE CANT MOVE FROM ONE MEMORY ADDRESS TO ANOTHER MEMORY ADDRESS, WE MUST USE AN AUXILARY REGISTER
    dec rcx
    dec r11
    ;;DECREMENT BOTH POINTERS, WHERE WE READ FROM AND WHERE WE WRITE TO 
    cmp r11, 0
    jge  "^shiftup^"\n\t\n 
  
  
  
  ;;RDX HOLDS THE NUMBER OF OPT ARGUMENTS
  dec rdx
  ;;RDX IS DECREMENTED CUZ WE WANT DONT WANT TO REMOVE THE LIST WE ADDED
  shl rdx, 3
    ;; MUL BY 8 = SHIFT 3, TO GET THE NUMBER OF BYTES IN ORDER TO ADD TO RSP POINTER
  
  
    add rsp, rdx   
  ;; NOW WE FIX THE STACK POINTER 
  ;; NOW THE STACK CONTAINS THE OPT-ARGS AS A LIST
    mov qword [rsp + WORD_SIZE * 2], " ^ (string_of_int ((List.length str_lst) + 1)) ^ 
  
    "\t\n ;;NUMBER OF ARGUMENTS ON THE STACK IS UPDATED BECAUSE OF THE OPT ARG
  
  ;;DONE SHRINKING STACK & ADJUST *********************************************************\n" ^
      
    doneadjust^":\n
  ;;AT THIS POINT WE FINISHED ADJUSTING THE STACK ACCORDING TO THE OPT PARAMS\t\n\t\n
      push rbp\n
      mov rbp, rsp\n" ^
      (generate_helper consts fvars expr (env_size+1)) ^ "\n
      leave\n
      ret\n" ^
      lcont^":\n\t\n"))

    
    | ScmApplicTP'(expr1, expr_lst) -> 
      (let lbls = idx_labels ["overwrite_frame"] in
      let overwrite = (List.nth lbls 0) in
      let rec applicLoop lst =
        match lst with
        |[] -> ""
        |hd::rest -> (generate_helper consts fvars hd env_size)^ "\npush rax\n" ^(applicLoop rest)   in

      (* (List.fold_left (fun acc param -> (generate_helper consts fvars param env_size) ^ "push rax\n" ^ acc) "" expr_lst) *)
      (applicLoop (List.rev expr_lst))
      ^"push " ^ string_of_int (List.length expr_lst) ^ "\n" ^
      (generate_helper consts fvars expr1 env_size) ^
      ";;APPLICTP IS HINNAAA\n "^ 

      "CLOSURE_ENV rbx, rax              ; rbx = rax -> env \n
      push rbx \n     
      ;; why plus one  
      push qword [rbp + WORD_SIZE * 1] \n ;push the old ret addr as a ret address for h
   
      
  
    ;; mov r8, PVAR(-1)                   ; r8 = n (= PVAR(-1) = old args num)
    mov r8, [rbp + 3*WORD_SIZE]  
    ;; r8 holds the number of params of the A frame
    add r8, 3                       
    ;; r8 holds the size of the A frame --> number of params + the lexenv + #params pushed + return addr
    shl r8, 3                       
    ;;multiplied by 8 SO -->r8 now holds the number of bytes held by the A frame
    add r8, rbp                     
    ;;now r8 points to the last param(An-1) of the A frame

    mov rbp, PVAR(-4)                ; rbp points to old rbp
    ;;above line same as mov rbp, [rbp]

    mov rcx, [rsp + WORD_SIZE * 2]   
    ;; RCX HOLDS THE NUMBER OF ARGS IN THE B FRAME = List.length lst_str 
    add rcx, 3                       
    ;;rcx now holds the size of the new B frame --> M+3 -> #ARGS + LEX + RET-ADDR
    
    " 
    ^overwrite ^":
    
    mov r13, qword [rsp + WORD_SIZE * (rcx - 1)]
    mov r13, qword [rsp + WORD_SIZE * (rcx +1 -2)]
    mov [r8], qword r13
    ;;SINCE WE CANT COPY FROM ONE MEMORY ADDRESS TO ANOTHER WE USE THE R13 REGISTER AS AN AUXILARY MEMORY STORAGE

    sub r8, WORD_SIZE
    ;;WE SUB BY WORDS_SIZE SINCE R8 IS IN BYTES
    ;;now we move to the next cell of the stack
    dec rcx
    cmp rcx,0
    jne " ^ overwrite ^ "
  
    add r8, WORD_SIZE               
    ;; R8 HOLDS THE RETURN ADDRESS TO F 
    mov rsp, r8    
    ;;NOW WE HAVE UPDATED THE RSP -> STACK POINTER                

    ;;NOW JUMP TO CODE OF CLOSURE
    CLOSURE_CODE rax, rax            ; rax = rax -> code
    jmp rax\n ")
      
    | _ -> ""    
    
    
    
    


  let make_consts_tbl asts =  
    (* [(ScmVoid, (0, "MAKE_VOID")); (ScmNil, (1, "MAKE_NIL")); (ScmBoolean false, (2, "MAKE_BOOL(0)")); (ScmBoolean true, (4, "MAKE_BOOL(1)"))] *)
    (* raise X_not_yet_implemented;; *)
    let basic_const_table = [(ScmVoid, (0, "MAKE_VOID")); (ScmNil, (1, "MAKE_NIL")); (ScmBoolean false, (2, "MAKE_BOOL(0)")); (ScmBoolean true, (4, "MAKE_BOOL(1)"))] in
    let all_consts = (List.fold_right (fun ast acc -> (find_consts ast) @ acc) asts []) in
    let set_consts = (omit_dup all_consts) in
    let extended_consts = (List.fold_right (fun ast acc -> (sub_constants ast) @ acc) set_consts []) in
    let set_extended_consts = (omit_dup extended_consts) in
    (**WE PASS THE INITAIL OFFSET AS 6 SINCE WE PUT THE NIL VOID AND BOOLEANS *)
    cct set_extended_consts 6  basic_const_table 
    



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
    "car";"set-car!";"cdr";"set-cdr!";"cons";"apply";
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
   (**TEST FUNCTION TO TEST THE FREE VARS AND CONSTANTS TABLE *) 
  let myGen e = 
   let fvar = make_fvars_tbl e in
   let myconsts = make_consts_tbl e in
   generate myconsts fvar (List.nth e 0);;
   (* "done" ;; *)
end;;

