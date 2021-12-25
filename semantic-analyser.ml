(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

#use "tag-parser.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type var' = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | ScmConst' of sexpr
  | ScmVar' of var'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmSet' of var' * expr'
  | ScmDef' of var' * expr'
  | ScmOr' of expr' list
  | ScmLambdaSimple' of string list * expr'
  | ScmLambdaOpt' of string list * string * expr'
  | ScmApplic' of expr' * (expr' list)
  | ScmApplicTP' of expr' * (expr' list);;


let var_eq v1 v2 =
match v1, v2 with
  | VarFree (name1), VarFree (name2) -> String.equal name1 name2
  | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
    major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
  | VarParam (name1, index1), VarParam (name2, index2) ->
       index1 = index2 && (String.equal name1 name2)
  | _ -> false

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
  | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                            (expr'_eq dit1 dit2) &&
                                              (expr'_eq dif1 dif2)
  | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
        List.for_all2 expr'_eq exprs1 exprs2
  | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
        (var_eq var1 var2) && (expr'_eq val1 val2)
  | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
     (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
      (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
  | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
  | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
  | _ -> false;;


module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val run_semantics : expr -> expr'
end;; (* end of module type SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct

  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

  let tag_lexical_address_for_var name params env = 
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> VarFree name
        | Some(major, minor) -> VarBound(name, major, minor))
    | Some minor -> VarParam(name, minor);;

  (* run this first! *)
  let annotate_lexical_addresses pe = 
   let rec run pe params env =
    match pe with
    |ScmConst(e) -> ScmConst'(e)
    |ScmVar(v)-> ScmVar'( tag_lexical_address_for_var v params env)

    | ScmIf(test, dit, dif) -> ScmIf'(run test params env , run dit params env, run dif params env) 
    | ScmSeq(expr_lst) -> ScmSeq'(List.map (fun expr -> run expr params env) expr_lst)
    | ScmSet(ScmVar expr1, expr2) -> ScmSet'(tag_lexical_address_for_var expr1 params env, run expr2 params env)
    | ScmDef(ScmVar expr1, expr2) -> ScmDef'(tag_lexical_address_for_var expr1 params env, run expr2 params env)  
    | ScmOr(expr_lst) -> ScmOr'(List.map (fun expr -> run expr params env) expr_lst)
    | ScmLambdaSimple(str_lst, expr1)-> ScmLambdaSimple'(str_lst, run expr1 (str_lst) (params::env))
    | ScmLambdaOpt(str_lst, str_opt, expr_body)->ScmLambdaOpt'(str_lst, str_opt, run expr_body (str_lst@[str_opt]) (params::env))
    | ScmApplic(expr1, expr_lst) ->ScmApplic'(run expr1 params env, List.map (fun expr -> run expr params env) expr_lst)
    |_-> raise X_this_should_not_happen


      (* raise X_not_yet_implemented  *)
   in 
   run pe [] [];;

   (* let run_lst lst params env = List.map (fun expr -> run expr params env) lst *)

  let rec rdc_rac s =
    match s with
    | [e] -> ([], e)
    | e :: s ->
       let (rdc, rac) = rdc_rac s
       in (e :: rdc, rac)
    | _ -> raise X_this_should_not_happen;;
  
  (* run this second! *)
  let annotate_tail_calls pe =
   let rec run pe in_tail = 
    (**in_tail indicates wether the current expr in tail position, chp5,pg41 *)
    match pe with
    | ScmConst' _ -> pe
    | ScmVar' _ -> pe
    (**If an if-expression is in tail-position, then the then-expression & else-expression are also in tail-position*)
    | ScmIf'(test, dit, dif) -> ScmIf'(run test false, run dit in_tail, run dif in_tail)
    | ScmSeq'(expr_lst) -> let (lst_except_last, last) = rdc_rac expr_lst in
                            ScmSeq'((List.map (fun(e)-> run e false) lst_except_last)@[(run last in_tail)])
    (**chp5,pg21  The body of a set!-expression is never in tail-position! *)
    | ScmSet'(expr1, expr2) -> ScmSet'( expr1, run expr2 false)
    | ScmDef'(expr1, expr2) -> ScmDef'(expr1, run expr2 in_tail)
    (** if an or-expression is in tail-position then its last expression is in tail-position *)
    | ScmOr'(expr_lst) -> let (lst_except_last, last) = rdc_rac expr_lst in
                            ScmOr'((List.map (fun(e)-> run e false) lst_except_last)@[(run last in_tail)])
    (** chp5, pg 41 Upon entering lambda-expressions (of any kind), the value of in_tp is reset back to true *)
    | ScmLambdaSimple'(str_lst, expr_body) -> ScmLambdaSimple'(str_lst,run expr_body true)
    | ScmLambdaOpt'(str_lst, str_opt,expr_body) -> ScmLambdaOpt'(str_lst, str_opt, run expr_body true) 
    | ScmApplic'(expr1, expr_lst) -> if in_tail then ScmApplicTP'(run expr1 false, (List.map (fun(e)-> run e false) expr_lst))
                                                else ScmApplic'(run expr1 false, (List.map (fun(e)-> run e false) expr_lst))
    | _ -> raise X_this_should_not_happen
      (* raise X_not_yet_implemented  *)
   in 
   run pe false;;

  (* boxing *)
  let rec read_write name expr onStack (r,w) =
    match expr with 
    | ScmConst' _-> (false,false)
    | ScmVar'(v) -> (((match v with
    |VarFree _ -> false
    |VarParam(vName,_) -> (name = vName)
    |VarBound(vName,_,_)-> (name = vName))||r),w)
    | ScmBox' _ -> (false,false)
    | ScmBoxGet' _-> (false,false)
    | ScmBoxSet'(v,expr1) -> read_write name expr1 onStack (r,w)
    | ScmIf'(test,dit,dif) -> let (tr,tw) = read_write name test onStack (r,w) in
                              let (ditr,ditw) = read_write name dit onStack (tr,tw) in
                              read_write name dif onStack (ditr,ditw)
    | ScmSeq'(expr_lst) -> List.fold_left (fun  (cr,cw) e -> let (er,ew)= read_write name e onStack (cr,cw) in ((cr||er),(cw||ew))) (r,w) expr_lst
    | ScmSet'(v,expr1) -> let (er,ew) = read_write name expr1 onStack (r,w) in
                          ((r||er),(ew||w||(match v with
                          |VarFree _ -> false
                          |VarParam(vName,_) -> (name = vName)
                          |VarBound(vName,_,_)-> (name = vName))))
    | ScmDef'(v,expr1) -> read_write name expr1 onStack (r,w)
    | ScmOr'(expr_lst) -> List.fold_left (fun  (cr,cw) e -> let (er,ew)= read_write name e onStack (cr,cw) in ((cr||er),(cw||ew))) (r,w) expr_lst
    | ScmLambdaSimple'(str_lst,expr1) -> if((not(List.mem name str_lst)) && (onStack=false)) then read_write name expr1 onStack (r,w) else (false,false)
    | ScmLambdaOpt'(str_lst,str_opt,expr1) -> if((not(List.mem name str_lst)) && (onStack=false)&& (not(str_opt=name))) then read_write name expr1 onStack (r,w) else (false,false)
    | ScmApplic'(expr1,expr_lst) -> 
      let (expr_r,expr_w) = (read_write name expr1 onStack (r,w)) in
      List.fold_left (fun  (cr,cw) e -> let (er,ew)= read_write name e onStack (cr,cw) in ((cr||er),(cw||ew))) (expr_r,expr_w) expr_lst
    | ScmApplicTP'(expr1, expr_lst) ->
      let (expr_r,expr_w) = read_write name expr1 onStack (r,w) in
      List.fold_left (fun  (cr,cw) e -> let (er,ew)= read_write name e onStack (cr,cw) in ((cr||er),(cw||ew))) (expr_r,expr_w) expr_lst

  let rec read_write_allribs name expr = 
    match expr with 
    | ScmConst' _->[]
    | ScmVar' _->[]
    | ScmBox' _->[]
    | ScmBoxGet' _ ->[]
    | ScmBoxSet'(v,expr1)-> read_write_allribs name expr1
    | ScmIf'(test,dit,dif) -> (read_write_allribs name test)@(read_write_allribs name dit)@(read_write_allribs name dif)
    | ScmSeq'(expr_lst) ->  List.fold_left (fun acc e -> acc @ (read_write_allribs name e)) [] expr_lst
    | ScmSet'(v,expr1) -> read_write_allribs name expr1
    | ScmDef'(v,expr1) -> read_write_allribs name expr1
    | ScmOr'(expr_lst) -> List.fold_left (fun acc e -> acc @ (read_write_allribs name e)) [] expr_lst
    | ScmLambdaSimple'(str_lst,expr1) -> if((List.mem name str_lst)) then [] else  [read_write name expr1 false (false,false)]
    | ScmLambdaOpt'(str_lst, str_opt, expr1)-> if((not(List.mem name str_lst)) && (not(name = str_opt))) then  [read_write name expr1 false (false,false)] else []
    | ScmApplic'(expr1,expr_lst)-> (read_write_allribs name expr1)@ (List.fold_left (fun acc e -> acc @ (read_write_allribs name e)) [] expr_lst)
    | ScmApplicTP'(expr1,expr_lst) -> (read_write_allribs name expr1)@ (List.fold_left (fun acc e -> acc @ (read_write_allribs name e)) [] expr_lst)

  let occs_on_stack_and_heap stack_read stack_write read_write_in_closures_lst =
    let (reads_in_lex, writes_in_lex) = List.fold_left (fun (sum_r, sum_w) (r, w) -> (sum_r + (Bool.to_int r), sum_w + (Bool.to_int w))) (0, 0) read_write_in_closures_lst in
    if ((stack_read && (writes_in_lex > 0)) || (*at least one read from stack and at least one write from lexical scope *)
       (stack_write && (reads_in_lex > 0)))    (*at least one write from stack and at least one read from lexical scope *)
      then true else false

  let occs_in_different_enclosing_env read_write_in_closures_lst =
    let (reads_in_lex, writes_in_lex) = List.fold_left (fun (sum_r, sum_w) (r, w) -> (sum_r + (Bool.to_int r), sum_w + (Bool.to_int w))) (0, 0) read_write_in_closures_lst in
    if(List.mem (true,true) read_write_in_closures_lst)
      then ((reads_in_lex > 1) || (writes_in_lex > 1)) (*there exits an enclosing environment with read and read occurence so to box we need an additional occurence in another enclosing environment*)
      else ((reads_in_lex > 0) && (writes_in_lex > 0)) (*thers is no read and write occurences in the same enclosing environment so the only option is read and write in different cosures*)


  let to_box name expr = (**CHANGE HERE*)
    let (read_from_stack, write_on_stack) = read_write name expr true (false, false) in
    let read_write_in_closures_list = read_write_allribs name expr in 
    (occs_in_different_enclosing_env read_write_in_closures_list)||( occs_on_stack_and_heap read_from_stack write_on_stack read_write_in_closures_list)

  let rec who_to_box lst body =
    (match lst with
    |[] -> []
    |first :: rest -> if( to_box (match first with  
                                  | VarParam(name, _) -> name
                                  | _ -> raise X_this_should_not_happen) body) then (first::(who_to_box rest body)) else (who_to_box rest body))
  

  let rec box_set expr =
  (* raise X_not_yet_implemented *)
  match expr with
  | ScmConst'(se) -> expr
  | ScmVar'(v) -> expr
  | ScmBox'(v)-> expr
  | ScmBoxGet'(v) -> expr
  | ScmBoxSet'(v,expr1) -> expr
  | ScmIf'(test, dit, dif) -> ScmIf'(box_set test, box_set dit, box_set dif)
  | ScmSeq'(expr_lst) ->  ScmSeq'(List.map box_set expr_lst)
  | ScmSet'(v,expr1)-> ScmSet'(v, box_set expr1)
  | ScmDef'(v, expr1) -> ScmDef'(v, box_set expr1)
  | ScmOr'(expr_lst)-> ScmOr'(List.map box_set expr_lst)
  | ScmLambdaSimple'(str_lst, expr_body) -> ScmLambdaSimple'(str_lst, box_inner_scope str_lst expr_body)
  | ScmLambdaOpt'(str_lst, str_opt, expr_body) -> ScmLambdaOpt'(str_lst, str_opt, box_inner_scope (str_lst@[str_opt]) expr_body)
  | ScmApplic'(expr1, expr_lst) -> ScmApplic'( box_set expr1, List.map box_set expr_lst)
  | ScmApplicTP'(expr1, expr_lst) -> ScmApplicTP'(box_set expr1, List.map box_set expr_lst)

  and box_inner_scope str_lst body  = 
    let var_params = (List.map (fun e -> let var = tag_lexical_address_for_var e str_lst [] in
                                                        (match var with
                                                        |VarParam(arg_name, minor)-> var
                                                        |_ -> raise X_this_should_not_happen) ) str_lst) in
    let params = who_to_box var_params body in   
    let set_params = List.map (fun v -> ScmSet'(v, ScmBox' v)) params in
    
    let rec box_set_get params body =
      match params with 
      |[] -> body
      |VarParam(name, _)::rest -> box_set_get  rest (box_p_in_body name body)
      |_-> raise X_this_should_not_happen
    in

    let boxed_body = box_set_get params body in
    let boxed_body = box_set boxed_body in
    let extended_body = (match (boxed_body) with 
      |ScmSeq' expr_lst -> ScmSeq'(set_params @ expr_lst)
      |_ -> if(List.length params = 0)
              then boxed_body (*none of the params need boxing*)
              else ScmSeq'(set_params @ [boxed_body])) in
    (box_set extended_body)
    
  and box_p_in_body pname expr =
    match expr with
    | ScmConst' _ -> expr
    | ScmVar'(v) -> (match v with
                            |VarFree _-> expr
                            |VarParam(name,minor) -> if(String.equal name pname) then ScmBoxGet'(v) else expr
                            |VarBound(name,major,minor)-> if(String.equal name pname) then ScmBoxGet'(v) else expr)
    | ScmBox' _ -> expr
    | ScmBoxGet' _ -> expr
    | ScmBoxSet'(v,expr1) -> ScmBoxSet'(v, box_p_in_body pname expr1)
    | ScmIf'(test, dit, dif) -> ScmIf'(box_p_in_body pname test, box_p_in_body pname dit, box_p_in_body pname dif)
    | ScmSeq'(expr_lst) -> ScmSeq'(List.map (fun(e)-> box_p_in_body pname e) expr_lst)
    | ScmSet'(v, expr1) -> (match v with
                            |VarFree _-> ScmSet'(v, box_p_in_body pname expr1)
                            |VarParam(name,minor) -> if(String.equal name pname) then ScmBoxSet'(v,expr1) else ScmSet'(v, box_p_in_body pname expr1)
                            |VarBound(name,major,minor)-> if(String.equal name pname) then ScmBoxSet'(v,expr1) else ScmSet'(v, box_p_in_body pname expr1))
    | ScmDef'(v,expr1) -> ScmDef'(v, box_p_in_body pname expr1)
    | ScmOr'(expr_lst) -> ScmOr'(List.map (fun(e)-> box_p_in_body pname e) expr_lst)
    | ScmLambdaSimple'(str_lst, expr_body) ->if (not(List.mem pname str_lst)) then ScmLambdaSimple'(str_lst, box_p_in_body pname expr_body) else expr
    | ScmLambdaOpt'(str_lst,str_opt,expr_body) -> if((not(List.mem pname str_lst))&&(not(String.equal pname str_opt)))
      then ScmLambdaOpt'(str_lst, str_opt, box_p_in_body pname expr_body) else expr
    | ScmApplic'(expr1, expr_lst) -> ScmApplic'(box_p_in_body pname expr1, List.map (fun(e)-> box_p_in_body pname e) expr_lst)
    | ScmApplicTP'(expr1,expr_lst) -> ScmApplicTP'(box_p_in_body pname expr1, List.map (fun(e)-> box_p_in_body pname e) expr_lst)


  let run_semantics expr =
    box_set
      (annotate_tail_calls
         (annotate_lexical_addresses expr))

end;; (* end of module Semantic_Analysis *)
