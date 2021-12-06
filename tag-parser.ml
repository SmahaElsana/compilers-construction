#use "reader.ml";;

type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;

exception X_my_exception;;
exception X_got_to_or;;
exception X_and_macro;;
exception X_if;;
exception X_bad_MIT;;
exception X_bad_letrec;;
exception X_bad_let;;
exception X_bad_lambda_body;;

exception X_vars_duplicated;;

let rec list_to_proper_list = function
| [] -> ScmNil
| hd::[] -> ScmPair (hd, ScmNil)
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec list_to_improper_list = function
| [] -> raise X_proper_list_error
| hd::[] -> hd
| hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
match scm_list with
| ScmNil -> sexpr
| ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
| _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))

let rec scm_map f sexpr =
match sexpr with
| ScmNil -> ScmNil
| ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
| _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
match sexpr1, sexpr2 with
| ScmNil, ScmNil -> ScmNil
| ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
| _, _ ->
    let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
    raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
| ScmNil -> []
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec scm_is_list = function
| ScmPair (hd, tl) -> scm_is_list tl
| ScmNil -> true
| _ -> false

let rec scm_list_length = function
| ScmPair (hd, tl) -> 1 + (scm_list_length tl)
| ScmNil -> 0
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec untag expr =
let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

let untag_lambda_opt vars var body =
let vars = match vars with
| [] -> ScmSymbol var
| _ -> list_to_improper_list (untag_vars (vars@[var])) in
list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

match expr with
| (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
| ScmConst s -> s
| ScmVar (name) -> ScmSymbol(name)
| ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
| ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
| ScmSeq(exprs) -> untag_tagged_list "begin" exprs
| ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
| ScmDef (var, value) -> untag_tagged_list "define" [var; value]
| ScmOr (exprs) -> untag_tagged_list "or" exprs
| ScmLambdaSimple (vars, ScmSeq(body)) ->
    let vars = list_to_proper_list (untag_vars vars) in
    let body = List.map untag body in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
| ScmLambdaSimple (vars, body) ->
    let vars = list_to_proper_list (untag_vars vars) in
    list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
| ScmLambdaOpt (vars, var, ScmSeq(body)) ->
    let body = List.map untag body in
    untag_lambda_opt vars var body
| ScmLambdaOpt (vars, var, body) ->
    let body = [untag body] in
    untag_lambda_opt vars var body
| ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;


let rec string_of_expr expr =
string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
match n1, n2 with
| ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
        numerator1 = numerator2 && denominator1 = denominator2
| ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
| _, _ -> false

let rec sexpr_eq s1 s2 =
match s1, s2 with
| (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
| ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
| ScmChar(char1), ScmChar(char2) -> char1 = char2
| ScmString(string1), ScmString(string2) -> String.equal string1 string2
| ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
| ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
| ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
| ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
| _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                            (expr_eq dit1 dit2) &&
                                              (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
        List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
        (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;


  let rec qq_helper ex = 
    (match ex with

    |ScmNil -> ScmPair(ScmSymbol "quote",ScmPair(ScmNil,ScmNil)) (*check this part again*)
    |ScmPair (ScmSymbol "unquote", ScmPair (ScmSymbol s, ScmNil)) -> (ScmSymbol s)
    |ScmSymbol _-> (ScmPair (ScmSymbol "quote", (ScmPair ( ex, ScmNil))))

    (* |ScmPair(ScmSymbol sym, rest)-> ScmPair(ScmSymbol "cons",ScmPair((ScmSymbol sym), (qq_helper rest))) *)    
    |ScmPair(ScmPair (ScmSymbol "unquote", ScmPair (ScmSymbol s, ScmNil)),rest)-> ScmPair(ScmSymbol "cons",ScmPair((ScmSymbol s),ScmPair((qq_helper rest),ScmNil)))
    
    |ScmPair(ScmPair (ScmSymbol "unquote-splicing", ScmPair (ScmSymbol s, ScmNil)),rest)-> ScmPair(ScmSymbol "append",ScmPair((ScmSymbol s),ScmPair((qq_helper rest),ScmNil)))
    
    |ScmPair(ScmSymbol "unquote-splicing",s1) -> ScmPair(ScmSymbol "quote",ScmPair ((ScmPair(ScmSymbol "unquote-splicing",s1)), ScmNil)) 

    (*recursive cases*)
    |ScmPair(ScmSymbol "unquote",ScmPair(sym, rest)) -> ScmPair(ScmPair(ScmSymbol "cons",ScmPair(sym,(qq_helper rest))),ScmNil)

    (* |ScmPair(ScmSymbol "unquote-splicing",ScmPair(sym,rest)) -> ScmPair(ScmPair(ScmSymbol "append",ScmPair(sym,(qq_helper rest))),ScmNil) *)
    
    (*base cases*)
    |ScmPair(ScmSymbol "unquote",s1) -> ex
    (* |ScmPair(ScmSymbol "unquote-splicing",s1) -> ScmPair(ScmSymbol "quote",ScmPair ((ScmPair(ScmSymbol "unquote-splicing",s1)), ScmNil))  *)

    (* |ScmPair(ScmSymbol "unquote-splicing",s1) -> raise X_my_exception *)
    
    
    |ScmVector(l) -> ScmPair (ScmSymbol "list->vector" ,ScmPair(qq_helper( list_to_proper_list l), ScmNil ))(*ScmVector(List.map qq_helper l)*)
    |ScmPair(ScmSymbol sym ,rest) -> ScmPair(ScmSymbol "cons",ScmPair(ScmPair(ScmSymbol "quote",ScmPair(ScmSymbol sym, ScmNil)),ScmPair((qq_helper rest),ScmNil)))
    |ScmPair(v ,rest)-> ScmPair(ScmSymbol "cons",ScmPair( qq_helper v ,ScmPair((qq_helper rest),ScmNil)))
    |_->ex
    );;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
end;; 

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;
(*helper function to check for duplications in sexpr list*)
let rec  check_duplications lst = 
  match lst with 
      |[]-> false 
      |hd::tl -> match (List.filter (fun a->(sexpr_eq a hd)) tl) with 
                  |[]->(check_duplications tl)
                  |_ ->true
;;    

let rec lambdaOpt_args_creat args lst = match args with         
        | ScmPair(ScmSymbol(s), rest) -> lambdaOpt_args_creat rest (lst@[s])
        | ScmSymbol(last) -> (lst, last)
        |_-> raise X_my_exception;;

let lambdaOpt_args args = lambdaOpt_args_creat args [];;

let rec simple_lambda_args_helper args lst = match args with         
        | ScmPair(ScmSymbol(s), rest) -> simple_lambda_args_helper rest (lst@[s])
        | ScmNil -> lst 
        | _-> raise X_my_exception;;

let simple_lambda_args args = simple_lambda_args_helper args [];;

let rec letrec_ribs ribs =
  (match ribs with
  | ScmNil -> ScmNil
  | ScmPair(ScmPair(ScmSymbol var, ScmPair(varval, ScmNil)), rest) -> ScmPair(ScmPair(ScmSymbol var, ScmPair(ScmPair(ScmSymbol "quote", ScmPair(ScmSymbol "whatever", ScmNil)), ScmNil)), (letrec_ribs rest))
  | _ -> raise X_my_exception);;

  let rec letrec_body ribs body =
    (match ribs with
    | ScmPair(ScmPair(var, ScmPair(varval, ScmNil)), rest) -> 
      ( ScmPair(ScmPair(ScmSymbol "set!", ScmPair(var, ScmPair(varval, ScmNil))), (letrec_body rest body)))
    |ScmPair(e, ScmNil)-> ScmPair(e,body)
    | ScmNil -> body
    | _ -> raise X_my_exception);;

let rec tag_parse_expression sexpr =
let sexpr = macro_expand sexpr in
match sexpr with 
(* Implement tag parsing here *)
(*2.1.1 constants*)
|ScmNil->(ScmConst ScmNil)
|ScmBoolean(b)-> ScmConst(ScmBoolean(b))
|ScmChar(c)-> ScmConst(ScmChar(c))
|ScmNumber(x)-> ScmConst(ScmNumber(x))
|ScmString(s)-> ScmConst(ScmString(s))
|ScmVector(v)-> ScmConst(ScmVector(v))
|(ScmPair (ScmSymbol "quote", (ScmPair (e, ScmNil)))) -> ScmConst(e)

(*2.1.2 variables*)
|ScmSymbol(s)-> if(List.mem s reserved_word_list) then raise (X_reserved_word s) else ScmVar(s)
(*2.1.3 conditionals*)
|ScmPair(ScmSymbol "if",ScmPair(cond, ScmPair (dit, dif)))-> 
  (match dif with
            |ScmNil-> ScmIf(tag_parse_expression cond, tag_parse_expression dit,ScmConst(ScmVoid))
            |ScmPair (a, ScmNil)-> ScmIf(tag_parse_expression cond,tag_parse_expression dit,tag_parse_expression a)
            (*please handle with many*)
            (* |ScmPair(car,cdr) -> ScmIf() *)
            |_ -> raise X_if)
(*2.1.4 disjunction*)
|ScmPair (ScmSymbol "or", sexpr_pairs) -> (match sexpr_pairs with
                                            |ScmNil -> ScmConst (ScmBoolean false)
                                            |ScmPair (sexp, ScmNil)-> tag_parse_expression sexp
                                            | ScmPair(sexpr1, cdr)-> ScmOr( List.map tag_parse_expression (scm_list_to_list sexpr_pairs))
                                            |_ -> raise X_got_to_or)
(*2.1.5 Lambda forms*)
|ScmPair(ScmSymbol "lambda",ScmPair(args, body))->(
  let lambda_body = (match body  with
            |ScmPair(car,ScmNil)-> tag_parse_expression car
            (* |ScmPair(car,cdr)->ScmSeq (List.map tag_parse_expression (scm_list_to_list body)) *)
            |ScmPair(car,cdr)->tag_parse_expression (ScmPair(ScmSymbol "begin",body))

            |_-> raise X_bad_lambda_body(**empty body*)) in
  if(scm_is_list args)
    (*simple lambda*)
  then(if(check_duplications (scm_list_to_list args)) 
          then raise X_vars_duplicated 
          else ScmLambdaSimple( (simple_lambda_args args),lambda_body))
    (*optional lambda*)
  else(let (args, last) = lambdaOpt_args args in ScmLambdaOpt(args, last, lambda_body)) (*need to check duplications for opt args*)
)

(*2.1.6 define (2)MIT define*)                                                        
|ScmPair(ScmSymbol "define",ScmPair(ScmPair(var,args),body)) ->(match var with
|ScmSymbol s -> ScmDef( (tag_parse_expression var),tag_parse_expression (ScmPair(ScmSymbol "lambda", ScmPair(args,body))))
|_->raise X_bad_MIT
)
  
(*2.1.6 define (1)simple define*)
|ScmPair(ScmSymbol "define", ScmPair(var_name, value)) ->( let exp_var_name = tag_parse_expression var_name in
                                                  (match value with
                                                        | ScmNil -> ScmDef (exp_var_name, ScmConst(ScmVoid)) (*check again HERE*)
                                                        | ScmPair(valSexp, ScmNil) -> ScmDef (exp_var_name, (tag_parse_expression valSexp)) 
                                                        | _ -> raise X_my_exception))

(*2.1.7 Assignments*)
(* |ScmPair(ScmSymbol "set!",ScmPair(varname, ScmPair(sexpr,ScmNil))) -> ScmPair(tag_parse_expression varname, tag_parse_expression sexpr ) *)
|ScmPair(ScmSymbol "set!",ScmPair(ScmSymbol var, ScmPair(sexpr,ScmNil))) -> ScmSet(tag_parse_expression(ScmSymbol var),tag_parse_expression sexpr )

(*2.1.9 Sequences*)
|ScmPair(ScmSymbol "begin",lst) -> (match lst with
  |ScmNil -> tag_parse_expression ScmNil
  |ScmPair(car,ScmNil)-> tag_parse_expression car
  |_-> ScmSeq(List.map tag_parse_expression (scm_list_to_list lst)))

(*2.1.8 Applications- should be last when tag parsing*)
|ScmPair(car,cdr)-> ScmApplic(tag_parse_expression car, List.map tag_parse_expression (scm_list_to_list cdr))

| _ -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized"))

and macro_expand sexpr =
match sexpr with
(* and *)
(*2.1.6 define (2)MIT define*)                                                        
(* |ScmPair(ScmSymbol "define",ScmPair(ScmPair(var,args),body)) ->
  ScmPair(ScmSymbol "define",ScmPair(var,(ScmPair(ScmSymbol "lambda", ScmPair(args,body))))) *)

| ScmPair(ScmSymbol "and", pairs) -> 
  (match pairs with
  |ScmNil -> ScmBoolean true
  |ScmPair(car, ScmNil)-> car
  |ScmPair(car,cdr)-> ScmPair(ScmSymbol "if",ScmPair(car, ScmPair (ScmPair(ScmSymbol "and", cdr), ScmPair(ScmBoolean(false),ScmNil)  )))
  |_-> raise X_and_macro
  )
(* Handle macro expansion patterns here *)
(*2.3 Expanding cond statements*)
|ScmPair(ScmSymbol "cond",ribs) ->(match ribs with

  |ScmPair(ScmPair(test,ScmPair(ScmSymbol "=>",ScmPair(dit,ScmNil))), seq) -> 
    (match seq with
    (*base case*)
    |ScmNil ->  macro_expand (ScmPair(ScmSymbol "let", ScmPair(ScmPair(ScmPair(ScmSymbol "value", ScmPair(test, ScmNil)), 
      ScmPair(ScmPair(ScmSymbol "f", ScmPair(ScmPair(ScmSymbol "lambda", ScmPair(ScmNil, ScmPair(dit, ScmNil))), ScmNil)), ScmNil)), 
      ScmPair(ScmPair(ScmSymbol "if", ScmPair(ScmSymbol "value", ScmPair(ScmPair(ScmPair(ScmSymbol "f", ScmNil), ScmPair(ScmSymbol "value", ScmNil)), ScmNil))), ScmNil))))
    
    |_ -> macro_expand(ScmPair(ScmSymbol "let", ScmPair(ScmPair(ScmPair(ScmSymbol "value", ScmPair(test, ScmNil)), 
      ScmPair(ScmPair(ScmSymbol "f", ScmPair(ScmPair(ScmSymbol "lambda", ScmPair(ScmNil, ScmPair(dit, ScmNil))), ScmNil)), 
      ScmPair(ScmPair(ScmSymbol "rest", ScmPair(ScmPair(ScmSymbol "lambda", ScmPair(ScmNil, ScmPair(ScmPair(ScmSymbol "cond", seq), ScmNil))), ScmNil)), ScmNil))), 
      ScmPair(ScmPair(ScmSymbol "if", ScmPair(ScmSymbol "value", ScmPair(ScmPair(ScmPair(ScmSymbol "f", ScmNil), ScmPair(ScmSymbol "value", ScmNil)), 
      ScmPair(ScmPair(ScmSymbol "rest", ScmNil), ScmNil)))), ScmNil))))
    )
  |ScmPair(ScmPair(ScmSymbol "else", rest),_)-> ScmPair(ScmSymbol "begin",rest)

  |ScmPair(ScmPair(test,cdr),rest) -> (match rest with 
      |ScmNil -> (ScmPair (ScmSymbol "if",ScmPair(test, ScmPair( ScmPair(ScmSymbol "begin", cdr),ScmNil))))
      |_ -> ScmPair(ScmSymbol "if",ScmPair(test,ScmPair(ScmPair(ScmSymbol "begin",cdr), ScmPair(ScmPair(ScmSymbol "cond",rest),ScmNil)))))
  |_-> raise X_my_exception
  )
(*2.4 Expanding let, let*, letrec*)
(*let*)
|ScmPair(ScmSymbol "let", ScmPair(ribs, body)) -> 
  (match ribs with
  | ScmNil ->  (ScmPair(ScmPair(ScmSymbol "lambda", ScmPair(ScmNil, body)), ScmNil))
  | ScmPair(first_rib, rest_ribs) ->

            let (vars, vals) =

              List.fold_right

                (fun rib_lst (vars, vals) ->
                    match rib_lst with
                    | ScmPair(var, ScmPair(value, ScmNil)) -> (ScmPair(var, vars), ScmPair(value, vals))
                    | _ -> raise X_my_exception) 

                (scm_list_to_list ribs) 
                (ScmNil, ScmNil) 
              in
             (ScmPair(ScmPair(ScmSymbol "lambda", ScmPair(vars, body)), vals))
  | _ -> raise X_my_exception)

(*let* *)
|ScmPair(ScmSymbol "let*",ScmPair(n_exps,body)) ->
  (match n_exps with
  |ScmNil -> macro_expand(ScmPair(ScmSymbol "let",ScmPair(ScmNil,body)))
  |ScmPair(r,ScmNil) -> macro_expand(ScmPair(ScmSymbol "let",ScmPair(ScmPair(r,ScmNil),body)))
  |ScmPair(r, ribs) -> macro_expand(ScmPair(ScmSymbol "let", ScmPair(ScmPair(r, ScmNil), ScmPair(ScmPair(ScmSymbol "let*", ScmPair(ribs, body)), ScmNil))))
  |_-> raise X_my_exception)

(*letrec*)
|ScmPair(ScmSymbol "letrec", ScmPair(ribs, body)) -> 
  (match ribs with 
  |ScmNil ->  macro_expand(ScmPair(ScmSymbol "let", ScmPair(ScmNil, body))) 
  | ScmPair(first_rib, rest_ribs) -> macro_expand(ScmPair(ScmSymbol "let", ScmPair((letrec_ribs ribs), (letrec_body ribs body))))
  |_ -> raise X_bad_letrec)

(*2.5 Handling quasiquote-expressions*)
|ScmPair(ScmSymbol "quasiquote", ScmPair(s, ScmNil)) -> (qq_helper s)

| _ -> sexpr
end;; 


