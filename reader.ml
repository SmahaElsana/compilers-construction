(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

 #use "pc.ml";;

 let rec gcd a b =
   match (a, b) with
   | (0, b) -> b
   | (a, 0) -> a
   | (a, b) -> gcd b (a mod b);;
 
 type scm_number =
   | ScmRational of (int * int)
   | ScmReal of float;;
 
 type sexpr =
   | ScmVoid
   | ScmNil
   | ScmBoolean of bool
   | ScmChar of char
   | ScmString of string
   | ScmSymbol of string
   | ScmNumber of scm_number
   | ScmVector of (sexpr list)
   | ScmPair of (sexpr * sexpr);;
 
 module type READER = sig
     val nt_sexpr : sexpr PC.parser
 end;; (* end of READER signature *)
 
 module Reader : READER = struct
 open PC;;
 
 let unitify nt = pack nt (fun _ -> ());;


 
 let rec nt_whitespace str =
   const (fun ch -> ch <= ' ') str
 and nt_end_of_line_or_file str =
   let nt1 = unitify (char '\n') in
   let nt2 = unitify nt_end_of_input in
   let nt1 = disj nt1 nt2 in
   nt1 str

 (* and nt_line_comment str =
 (* let nt_end = disj (unitify (char '\n')) (unitify nt_end_of_input) in *)
 let nt_end = disj_list[ (unitify (char '\n'))] in
 let nt1 = char ';' in
 let nt2 = diff nt_any nt_end in
 let nt2 = star nt2 in
 let nt1 = caten nt1 (caten nt2 nt_end) in 
 let nt1 = unitify nt1 in 
 nt1 str *)

 and nt_line_comment str =
 let prefix = word ";" in
 (* unitify(pack (caten prefix nt_inner_comment) (fun (temp) -> ScmNil)) str  *)
 (* unitify(pack (caten prefix nt_sexpr) (fun (temp) -> ScmNil)) str  *)
 let nt0 = diff nt_any (char (char_of_int 10)) in
 let nt0 = star nt0 in
 let nt1 = caten prefix nt0 in
 let nt1 =(pack nt1 (function (_) -> ScmNil)) in
 let nt1 = unitify(nt1) in 
 nt1 str

 
 (* and nt_paired_comment str =
   let nt1 = char '{' in
   let nt2 = disj_list[unitify nt_char; unitify nt_string; unitify nt_comment] in
   let nt2' = disj nt2 (unitify (one_of "{}")) in
   let nt3 = diff nt_any nt2' in
   let nt3 = unitify nt3 in
   let nt3 = disj nt3 nt2 in
   let nt3 = star nt3 in
   let nt4 = char '}' in
   (* let nt1 = unitify (caten nt1 (caten nt3 nt4)) in *)
   let nt1 = (caten nt1 (caten nt3 nt4)) in

   nt1 str; *)

 (* and nt_matching_comment str = *)
  and nt_paired_comment str =
  let nt1 = char '{' in
  let nt2 = char '}' in
  let nt3 = star (diff (diff nt_any (char '{')) (char '}')) in
  let nt4 = caten nt1 (caten nt3 nt2) in 
  let nt5 = star nt4 in
  let nt6 = caten nt1 (caten nt5 nt2) in 
  let nt7 = (pack nt6 (function (_) -> ScmNil)) in
  let nt7 = unitify(nt7) in 
  nt7 str


   
 

 and nt_sexpr_comment str = 
 let prefix = word "#;" in
 (* unitify(pack (caten prefix nt_inner_comment) (fun (temp) -> ScmNil)) str  *)
 (* unitify(pack (caten prefix nt_sexpr) (fun (temp) -> ScmNil)) str  *)
 let nt1 = caten prefix nt_sexpr in
 let nt1 =(pack nt1 (fun (_) -> ScmNil)) in
 (* let nt1 = unitify(nt1) in  *)
 nt1 str

 (* and nt_mycomment str = 
  let nt1 = caten (char '#') (char ';') in
  let nt1 = pack nt1 (function(_)-> ScmNil) in
  nt1 str *)

 and nt_comment str =
   disj_list
     [
      nt_line_comment;
      nt_paired_comment;
      unitify (nt_sexpr_comment);
      ] str
 and nt_skip_star str =
   let nt1 = disj (unitify nt_whitespace) nt_comment in
   let nt1 = unitify (star nt1) in
   nt1 str
 and make_skipped_star (nt : 'a parser) =
   let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
   let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
   nt1
 and nt_natural str =
 let nt1 = range '0' '9' in
 let nt1 = plus nt1 in
 let nt2 = pack nt1 (fun (a)-> int_of_string(list_to_string(a))) in
 nt2 str
 and nt_sign str = 
 let nt1 = disj_list[(char '-') ;(char '+')]  in
 nt1 str
 and read_int str = let nt1 = maybe (nt_sign) in
 let nt2 = caten nt1 nt_natural in
 nt2 str
 and nt_int str = 
 let nt1 = maybe (nt_sign) in
 let nt2 = caten nt1 nt_natural in
 let nt3 = pack nt2 (fun(sign, num)->match sign with
                                 |Some '-' -> (-1)*num
                                 |Some '+' -> num
                                 |None ->num
                                 |_->num) in
 nt3 str
 and nt_fl str = 
 let nt1 = maybe (nt_sign) in
 let nt2 = caten nt1 (plus (range '0' '9')) in
 let nt3 = pack nt2 (fun(sign, num)->match sign with
                                 |Some '-' -> (-1.)*.float_of_string(list_to_string(num))
                                 |Some '+' -> float_of_string(list_to_string(num))
                                 |None ->float_of_string(list_to_string(num))
                                 |_-> float_of_string(list_to_string(num))) in
 nt3 str
 
 and nt_frac str = 
 let nt1 = caten nt_int (caten (char '/') nt_natural) in
 let nt2 = pack nt1 (fun(nom,(_, den))-> let gcdRes = gcd (abs nom) den in
                                         ScmRational(nom/gcdRes , den/gcdRes)) in
 nt2 str
 and nt_integer_part str = 
 let nt1 = range '0' '9' in
 let nt1 = plus nt1 in
 let nt2 = pack nt1 (fun (mant)-> float_of_string(list_to_string(mant))) in
 nt2 str
 and nt_mantissa str = 
 let nt1 = range '0' '9' in
 let nt1 = plus nt1 in
 let nt2 = pack nt1 (fun (mant)-> float_of_string("0."^list_to_string(mant))) in
 nt2 str
 
 and nt_exp_token str = 
 let nt1 = disj_list[(word_ci "e"); (word "*10^");(word "*10**")] in
 (pack nt1 (fun _ -> 'e')) str
 (* let nt1 = unitify nt1 in *)
 (* nt1 str *)
 
 and nt_exponent str = 
 let nt1 = (caten nt_exp_token nt_int) in
 let nt2 = pack nt1 (fun(e,expo)-> 10.**(float_of_int expo)) in
 nt2 str

 and nt_floatA str =
 let nt1 = caten nt_integer_part 
                 (caten (char '.')
                        (caten (maybe nt_mantissa)
                               (maybe nt_exponent))) in
 let nt2 = pack nt1 (fun(intPrt,(dot,(man, exp)))-> match man,exp with 
                                                               |None,None -> intPrt
                                                               |None,Some e -> intPrt *. e 
                                                               |Some m,None -> intPrt +. m
                                                               |Some m,Some e ->(intPrt +. m) *. e) in
 nt2 str
 and nt_floatB str = 
 let nt1 = caten (char '.') (caten nt_mantissa (maybe nt_exponent)) in
 let nt2 = pack nt1 (fun (dot,(man,exp))-> match exp with
                                                   |Some exponent ->  man *. exponent
                                                   |None -> man
                                                   ) in
 nt2 str
 
 and nt_floatC str =
 let nt1 = caten nt_integer_part nt_exponent in
 let nt2 = pack nt1 (fun(num,exp)-> (num *. ( exp)))in
 nt2 str
 (* and nt_float str = 
 let nt1 = pack (disj_list[(nt_floatA);(nt_floatB);(nt_floatC)]) (fun(v)-> ScmReal v) in
 nt1 str *)
 and nt_float str = 
 let nt1 = maybe(nt_sign) in
 let nt2 = disj_list[(nt_floatA);(nt_floatB);(nt_floatC)] in
 let nt1 = caten nt1 nt2 in
 let nt1 = pack nt1 (fun(sign,n)-> match sign with
                                              |Some '-' -> ScmReal(-1. *. n)
                                              |Some '+' -> ScmReal(n)
                                              |_-> ScmReal(n)) in
  nt1 str


 (* let nt1 = pack (disj_list[(nt_floatA);(nt_floatB);(nt_floatC)]) (fun(v)-> ScmReal v) in
 nt1 str *)
 and nt_number str =
   let nt1 = nt_float in
   let nt2 = nt_frac in
   let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
   let nt1 = disj nt1 (disj nt2 nt3) in
   let nt1 = pack nt1 (fun r -> ScmNumber r) in
   let nt1 = not_followed_by nt1 nt_symbol_char in
   nt1 str
 and nt_boolean str = 
 let nt1 = word_ci "#f" in
   let nt1 = pack nt1 (function _-> false) in
   let nt2 = word_ci "#t" in
   let nt2 = pack nt2 (function _-> true) in
   let nt1 = disj nt1 nt2 in
   let nt1 = pack nt1 (function b-> ScmBoolean b) in
   nt1 str
 
 and  nt_VisibleSimpleChaar str =
 let nt1 = const (fun ch -> ch > (char_of_int 32)) in
 (**added this line to check when arc after char*)
 let nt2 = const (fun ch -> ((ch > (char_of_int 55)) && ((ch < (char_of_int 122))))) in
 let nt1 = not_followed_by nt1 nt2 in
 nt1 str
 
 
 and nt_char_simple str = const (fun ch -> (int_of_char ch) > 32)
 
 and make_named_char char_name ch = pack (word_ci char_name) (fun e -> ch)
 
 and nt_char_named str =
   let nt1 =
     disj_list [(make_named_char "newline" '\n');
                (make_named_char "page" '\012');
                (make_named_char "return" '\r');
                (make_named_char "space" ' ');
                (make_named_char "tab" '\t');
                (make_named_char "nul" (char_of_int 0))] in
   nt1 str

 and nt_char_hex str = disj_list[(range_ci 'a' 'f');(range '0' '9');] str
 
 and nt_HexadecimalChar str = 
 let nt1 = char_ci 'x' in
 (**let nt1 = word "\\x and \\X"*)
 let nt2 = plus nt_char_hex in
 let nt2 = caten nt1 nt2 in
 let nt3 = pack nt2 (fun( prex, hexL)-> char_of_int(int_of_string("0x"^list_to_string(hexL))) ) in
 nt3 str
 
 and nt_charPrefix str = (word "#\\") str
 
 and nt_char str = 
 let nt1 = disj_list[(nt_HexadecimalChar);(nt_char_named);(nt_VisibleSimpleChaar);] in
 let nt2 = caten nt_charPrefix nt1 in
 let nt3 = pack nt2 (fun(pre,ch)-> ScmChar ch) in
 nt3 str
 
 and nt_symbol_char str =  disj_list[(range '0' '9');
 (range 'a' 'z');
 (range 'A' 'Z');
 (char '!');
 (char '$');
 (char '^');
 (char '*');
 (char '-');
 (char '_');
 (char '=');
 (char '+');
 (char '<');
 (char '>');
 (char '?');
 (char ':');
 (char '/');] str
 
 and nt_symbol str =
   let nt1 = plus nt_symbol_char in
   let nt1 = pack nt1 (list_to_string) in
   let nt1 = pack nt1 (fun name -> ScmSymbol (String.lowercase_ascii name)) in
   let nt1 = diff nt1 nt_number in
   nt1 str
 
 and nt_stringLiteralChar str = 
 let nt1 = diff nt_any (disj 
 (char(char_of_int(126))) 
 (disj  (char(char_of_int(92))) (char(char_of_int(34))) )) in
 nt1 str

 and nt_string_hex_char str =
 (* let nt1 = char_ci 'x' in
 (**let nt1 = word "\\x and \\X"*)
 let nt2 = plus nt_char_hex in
 let nt2 = caten nt1 (caten nt2 (char ';')) in
 let nt3 = pack nt2 (fun( prex, (hexL,e))-> char_of_int(int_of_string("0x"^list_to_string(hexL))) ) in
 nt3 str *)
 
 let nt2 = plus nt_char_hex in
 let nt2 = caten (char '\\') (caten (char_ci 'x') (caten nt2 (char ';'))) in
 let nt3 = pack nt2 (fun(prefex,(xletter,(hexL,e)))-> char_of_int(int_of_string("0x"^list_to_string(hexL))) ) in
 nt3 str
 
 (* let prefex = word "\\x" in
 let plusHex = plus nt_char_hex in
 let nt1 = caten (prefex (caten plusHex (char ';'))) in
 let nt2 = pack nt1 (fun(pre,(listx,end))-> list_to_string listx) in
 nt2 str *)
 and nt_string_meta_char str = 
 PC.disj_list [
     PC.pack (PC.word "\\r") (fun (temp) -> char_of_int(13))
     ; PC.pack (PC.word "\\n") (fun (temp) -> char_of_int(10))
     ; PC.pack (PC.word "\\t") (fun (temp) -> char_of_int(9))
     ; PC.pack (PC.word "\\f") (fun (temp) -> char_of_int(12))
     ; PC.pack (PC.word "\\\\") (fun (temp) -> char_of_int(92))
     ; PC.pack (PC.word "\\\"") (fun (temp) -> char_of_int(34))
     ; PC.pack (PC.word "~~") (fun (temp) -> char_of_int(126))
   ] str
 
 (* and nt_StringInterpolated str = 
 let nt0 = star nt_whitespace in
 let nt1 = caten (char '~')
          (caten (char '{')
              (caten (nt0 
              (caten (star nt_sexpr) 
                 (caten nt0(char '}'))
               )
                 ))) in
 let nt2 = pack nt1 (fun((tilda,(lb,(lsps,(data,(rsps,rb))))))-> ScmPair(ScmSymbol("format"),ScmPair("a",ScmNil))) in
 nt2 str *)

 and nt_StringInterpolated str = 
 let nt1 = word "~{" in
 let nt1 = caten nt1 nt_sexpr in
 let nt1 = caten nt1 (word "}") in
 let nt1 = pack nt1 (fun((a,b),c) -> ScmPair(ScmSymbol("format"),ScmPair(ScmString("~a"),ScmPair(b,ScmNil)))) in
 nt1 str
 
 and nt_stringchar str = disj_list [(nt_stringLiteralChar);(nt_string_hex_char);(nt_string_meta_char)] str
 and nt_string str = 
 let nt1 = caten (char '"') (caten (star nt_stringchar) (char '"')) in
 let nt2 = pack nt1 (fun((l,(data,r)))-> ScmString (list_to_string data)) in
 nt2 str
 
 and nt_vector str =
   let nt1 = word "#(" in
   let nt2 = caten nt_skip_star (char ')') in
   let nt2 = pack nt2 (fun _ -> ScmVector []) in
   let nt3 = plus nt_sexpr in
   let nt4 = char ')' in
   let nt3 = caten nt3 nt4 in
   let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
   let nt2 = disj nt2 nt3 in
   let nt1 = caten nt1 nt2 in
   let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
   nt1 str
 
   and properList str = 
   let nt1 = caten (word "(") (caten (star nt_sexpr) (word ")")) in

   (* (fun (_, ((lp,(exp,rp)), _)) -> exp) *)
   (* pack nt1 (fun(lp,(exp,rp))-> match exp with *)
    pack nt1 (fun(_,(exp,_))-> match exp with

   | []-> ScmNil
   | _ -> List.fold_right (fun a b -> ScmPair(a,b)) exp ScmNil) str
   
   and improperList str = 
   let nt1 = caten (word "(")  (caten (plus nt_sexpr) (caten (word ".") (caten nt_sexpr (word")")))) in 
   pack nt1 (fun (lp ,(strdexp ,(dot,(exp, rp))))-> match strdexp with
   _ -> List.fold_right(fun a b -> ScmPair(a,b)) strdexp exp)
   str
   
 and nt_list str = (disj improperList properList) str
 
 and nt_quoted str =
   let quote = word "'" in
   pack (caten quote nt_sexpr) (fun(a,b)->ScmPair(ScmSymbol("quote"),ScmPair(b,ScmNil))) str
 
 and nt_quasiquoted str = 
   let quasi = word "`" in
   pack (caten quasi nt_sexpr) (fun(a,b)->ScmPair(ScmSymbol("quasiquote"),ScmPair(b,ScmNil))) str
 
 and nt_unquoted str =
   let unquote = word "," in
   pack (caten unquote nt_sexpr) (fun(a,b)->ScmPair(ScmSymbol("unquote"),ScmPair(b,ScmNil))) str
 
 and nt_unquoteSpliced str =
   let unqtsplcd = word ",@" in
   pack (caten unqtsplcd nt_sexpr) (fun(a,b)->ScmPair(ScmSymbol("unquote-splicing"),(ScmPair(b,ScmNil)))) str
 
 and nt_quoted_forms str = disj_list[(nt_quoted);(nt_quasiquoted);(nt_unquoted);(nt_unquoteSpliced)] str
 and nt_sexpr str = 
   let nt1 =
     disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
                nt_string; nt_vector; nt_list; nt_quoted_forms;] in
   let nt1 = make_skipped_star nt1 in
   nt1 str;
 end;; (* end of struct Reader *)
 
 let rec string_of_sexpr = function
   | ScmVoid -> "#<void>"
   | ScmNil -> "()"
   | ScmBoolean(false) -> "#f"
   | ScmBoolean(true) -> "#t"
   | ScmChar('\n') -> "#\\newline"
   | ScmChar('\r') -> "#\\return"
   | ScmChar('\012') -> "#\\page"
   | ScmChar('\t') -> "#\\tab"
   | ScmChar(' ') -> "#\\space"
   | ScmChar(ch) ->
      if (ch < ' ')
      then let n = int_of_char ch in
           Printf.sprintf "#\\x%x" n
      else Printf.sprintf "#\\%c" ch
   | ScmString(str) ->
      Printf.sprintf "\"%s\""
        (String.concat ""
           (List.map
              (function
               | '\n' -> "\\n"
               | '\012' -> "\\f"
               | '\r' -> "\\r"
               | '\t' -> "\\t"
               | ch ->
                  if (ch < ' ')
                  then Printf.sprintf "\\x%x;" (int_of_char ch)
                  else Printf.sprintf "%c" ch)
              (string_to_list str)))
   | ScmSymbol(sym) -> sym
   | ScmNumber(ScmRational(0, _)) -> "0"
   | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
   | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
   | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
   | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
   | ScmVector(sexprs) ->
      let strings = List.map string_of_sexpr sexprs in
      let inner_string = String.concat " " strings in
      Printf.sprintf "#(%s)" inner_string
   | ScmPair(ScmSymbol "quote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf "'%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "quasiquote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf "`%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "unquote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf ",%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "unquote-splicing",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf ",@%s" (string_of_sexpr sexpr)
   | ScmPair(car, cdr) ->
      string_of_sexpr' (string_of_sexpr car) cdr
 and string_of_sexpr' car_string = function
   | ScmNil -> Printf.sprintf "(%s)" car_string
   | ScmPair(cadr, cddr) ->
      let new_car_string =
        Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
      string_of_sexpr' new_car_string cddr
   | cdr ->
      let cdr_string = (string_of_sexpr cdr) in
      Printf.sprintf "(%s . %s)" car_string cdr_string;;