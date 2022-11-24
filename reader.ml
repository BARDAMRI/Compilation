#use "pc.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen of string;;

let rec is_member a = function
  | [] -> false
  | a' :: s -> (a = a') || (is_member a s);;

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
  val print_sexpr : out_channel -> sexpr -> unit
  val print_sexprs : out_channel -> sexpr list -> unit
  val sprint_sexpr : 'a -> sexpr -> string
  val sprint_sexprs : 'a -> sexpr list -> string
  val scheme_sexpr_list_of_sexpr_list : sexpr list -> sexpr
end;; (* end of READER signature *)

module Reader : READER = struct
  open PC;;

  type string_part =
    | Static of string
    | Dynamic of sexpr;;

  let unitify nt = pack nt (fun _ -> ());;

  let rec nt_whitespace str =
    const (fun ch -> ch <= ' ') str
  and nt_end_of_line_or_file str = 
    let nt1 = unitify (char '\n') in
    let nt2 = unitify nt_end_of_input in
    let nt1 = disj nt1 nt2 in
    nt1 str
  and nt_line_comment str =
    let nt1 = char ';' in
    let nt2 = diff nt_any nt_end_of_line_or_file in
    let nt2 = star nt2 in
    let nt1 = caten nt1 nt2 in
    let nt1 = caten nt1 nt_end_of_line_or_file in
    let nt1 = unitify nt1 in
    nt1 str
  and nt_paired_comment str = raise X_not_yet_implemented
  and nt_sexpr_comment str = raise X_not_yet_implemented
  and nt_comment str =
    disj_list
      [nt_line_comment;
       nt_paired_comment;
       nt_sexpr_comment] str
  and nt_void str =
    let nt1 = word_ci "#void" in
    let nt1 = not_followed_by nt1 nt_symbol_char in
    let nt1 = pack nt1 (fun _ -> ScmVoid) in
    nt1 str
  and nt_skip_star str =
    let nt1 = disj (unitify nt_whitespace) nt_comment in
    let nt1 = unitify (star nt1) in
    nt1 str
  and make_skipped_star (nt : 'a parser) =
    let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
    let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
    nt1
  and nt_digit str = 
    let nt1 = const (fun ch -> '0' <= ch && ch <= '9' ) in
    let ascii_0 = int_of_char '0' in
    let nt2 = pack nt1 (fun ch -> (int_of_char ch) - ascii_0 ) in
    nt2 str
  and nt_hex_digit str = raise X_not_yet_implemented
  and nt_nat =
    let rec nt str =
      pack (caten nt_digit (disj nt nt_epsilon)) (function (a, s) -> a :: s) str in
      pack nt (fun s -> (List.fold_left (fun a b -> 10 * a + b) 0 s))
  and nt_hex_nat str = 
    let nt1 = plus nt_hex_digit in
    let nt1 = pack nt1
                (fun digits ->
                  List.fold_left
                    (fun num digit ->
                      16 * num + digit)
                    0
                    digits) in
    nt1 str
  and nt_optional_sign str =
    let nt1 = const (fun ch -> '+'== ch ) in
    let nt2  = const (fun ch-> '-'== ch ) in
    let nt3  = pack nt1 (fun ch -> true) in 
    let nt4 = pack nt2 (fun ch -> false) in
    let nt5 = disj nt3 nt4 in
    nt5 str
  and nt_int str =
    let nt1 = caten nt_optional_sign nt_nat in
    let nt1 = pack nt1
                (fun (is_positive, n) ->
                  if is_positive then n else -n) in
    nt1 str
  and nt_frac str =
    let nt1 = caten nt_int (char '/') in
    let nt1 = pack nt1 (fun (num, _) -> num) in
    let nt2 = only_if nt_nat (fun n -> n != 0) in
    let nt1 = caten nt1 nt2 in
    let nt1 = pack nt1
                (fun (num, den) ->
                  let d = gcd num den in
                  ScmRational(num / d, den / d)) in
    nt1 str
  and nt_integer_part str =
    let nt1 = plus nt_digit in
    let nt1 = pack nt1
                (fun digits ->
                  List.fold_left
                    (fun num digit -> 10.0 *. num +. (float_of_int digit))
                    0.0
                    digits) in
    nt1 str
  and nt_mantissa str =
    let nt1 = plus nt_digit in
    let nt1 = pack nt1
                (fun digits ->
                  List.fold_right
                    (fun digit num ->
                      ((float_of_int digit) +. num) /. 10.0)
                    digits
                    0.0) in
    nt1 str
  and nt_exponent str =
    let nt1 = unitify (char_ci 'e') in
    let nt2 = word "*10" in
    let nt3 = unitify (word "**") in
    let nt4 = unitify (char '^') in
    let nt3 = disj nt3 nt4 in
    let nt2 = caten nt2 nt3 in
    let nt2 = unitify nt2 in
    let nt1 = disj nt1 nt2 in
    let nt1 = caten nt1 nt_int in
    let nt1 = pack nt1 (fun (_, n) -> Float.pow 10. (float_of_int n)) in
    nt1 str
  and nt_floatA str =
    let nt1 = nt_nat in
    let nt2 = char '.' in
    let nt3 = make_maybe nt_mantissa in
    let nt4 = make_maybe nt_exponent in
    let nt5 = caten nt1 (caten nt2 ( caten nt3 nt4)) in
    nt5 str
  and nt_floatB str =
    let nt1 = char '.' in
    let nt2 = nt_mantissa in
    let nt3 = make_maybe nt_exponent in
    let nt4 = caten nt1 (caten nt2 nt3) in
    nt4 str
  and nt_floatC str = 
    let nt1 = nt_nat in
    let nt2 = nt_exponent in
    let nt3 = caten  nt1 nt2  in
    nt3 str
  and nt_float str =
    let nt1 = nt_optional_sign in
    let nt2 = nt_floatA in
    let nt3 = nt_floatB in
    let nt4 = nt_floatC in
    let nt5 = disj nt2 nt3 nt4 in
    let nt6 = caten nt1 nt5 in
    nt6 str
                      
  and nt_number str =
    let nt1 = nt_float in
    let nt2 = nt_frac in
    let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
    let nt1 = disj nt1 (disj nt2 nt3) in
    let nt1 = pack nt1 (fun r -> ScmNumber r) in
    let nt1 = not_followed_by nt1 nt_symbol_char in
    nt1 str  
  and nt_boolean str =
    let nt1 = char '#' in
    let nt2 = char_ci 'f' in
    let nt2 = pack nt2 (fun _ -> ScmBoolean false) in
    let nt3 = char_ci 't' in
    let nt3 = pack nt3 (fun _ -> ScmBoolean true) in
    let nt2 = disj nt2 nt3 in
    let nt1 = caten nt1 nt2 in
    let nt1 = pack nt1 (fun (_, value) -> value) in
    let nt2 = nt_symbol_char in
    let nt1 = not_followed_by nt1 nt2 in
    nt1 str
  and nt_char_simple str =
    let nt1 = const(fun ch -> ' ' < ch) in
    let nt1 = not_followed_by nt1 nt_symbol_char in
    nt1 str
  and nt_char_named str = raise X_not_yet_implemented
  and nt_char_hex str =
    let nt1 = caten (char_ci 'x') nt_hex_nat in
    let nt1 = pack nt1 (fun (_, n) -> n) in
    let nt1 = only_if nt1 (fun n -> n < 256) in
    let nt1 = pack nt1 (fun n -> char_of_int n) in
    nt1 str  
  and nt_char str =
    let nt1 = word "#\\" in
    let nt2 = disj nt_char_simple (disj nt_char_named nt_char_hex) in
    let nt1 = caten nt1 nt2 in
    let nt1 = pack nt1 (fun (_, ch) -> ScmChar ch) in
    nt1 str
  and nt_symbol_char str =
    let nt1 = range_ci 'a' 'z' in
    let nt1 = pack nt1 Char.lowercase_ascii in
    let nt2 = range '0' '9' in
    let nt3 = one_of "!$^*_-+=<>?/" in
    let nt1 = disj nt1 (disj nt2 nt3) in
    nt1 str
  and nt_symbol str = raise X_not_yet_implemented
  and nt_string_part_simple str =
    let nt1 =
      disj_list [unitify (char '"'); unitify (char '\\'); unitify (word "~~");
                 unitify nt_string_part_dynamic] in
    let nt1 = diff nt_any nt1 in
    nt1 str
  and nt_string_part_meta str =
    let nt1 =
      disj_list [pack (word "\\\\") (fun _ -> '\\');
                 pack (word "\\\"") (fun _ -> '"');
                 pack (word "\\n") (fun _ -> '\n');
                 pack (word "\\r") (fun _ -> '\r');
                 pack (word "\\f") (fun _ -> '\012');
                 pack (word "\\t") (fun _ -> '\t');
                 pack (word "~~") (fun _ -> '~')] in
    nt1 str
  and nt_string_part_hex str =
    let nt1 = word_ci "\\x" in
    let nt2 = nt_hex_nat in
    let nt2 = only_if nt2 (fun n -> n < 256) in
    let nt3 = char ';' in
    let nt1 = caten nt1 (caten nt2 nt3) in
    let nt1 = pack nt1 (fun (_, (n, _)) -> n) in
    let nt1 = pack nt1 char_of_int in
    nt1 str
  and nt_string_part_dynamic str = raise X_not_yet_implemented
  and nt_string_part_static str =
    let nt1 = disj_list [nt_string_part_simple;
                         nt_string_part_meta;
                         nt_string_part_hex] in
    let nt1 = plus nt1 in
    let nt1 = pack nt1 string_of_list in
    let nt1 = pack nt1 (fun str -> Static str) in
    nt1 str
  and nt_string_part str =
    disj nt_string_part_static nt_string_part_dynamic str
  and nt_string str =
    let nt1 = char '"' in
    let nt2 = star nt_string_part in
    let nt3 = char '"' in
    let nt1 = caten nt1 (caten nt2 nt3) in
    let nt1 = pack nt1 (fun (_, (parts, _)) -> parts) in
    let nt1 = pack nt1
                (fun parts ->
                  match parts with
                  | [] -> ScmString ""
                  | [Static(str)] -> ScmString str
                  | [Dynamic(sexpr)] -> sexpr
                  | parts ->
                     let argl =
                       List.fold_right
                         (fun car cdr ->
                           ScmPair((match car with
                                    | Static(str) -> ScmString(str)
                                    | Dynamic(sexpr) -> sexpr),
                                   cdr))
                         parts
                         ScmNil in
                     ScmPair(ScmSymbol "string-append", argl)) in
    nt1 str
  and nt_vector str =
    let nt1 = word '#' in
    let nt2 = word '(' in 
    let nt3 = caten nt1 nt2 in
    let nt4 = nt_sexpr in
    let nt5 = caten nt4 (nt_skip_star) in
    let nt6 = caten nt3 nt5 in
    let nt7 = word ')' in
    let nt8 = caten nt6 nt7 in
    nt8 str
    
  and nt_list str = raise X_not_yet_implemented
  and make_quoted_form nt_qf qf_name =
    let nt1 = caten nt_qf nt_sexpr in
    let nt1 = pack nt1
                (fun (_, sexpr) ->
                  ScmPair(ScmSymbol qf_name,
                          ScmPair(sexpr, ScmNil))) in
    nt1
  and nt_quoted_forms str =
    let nt1 =
      disj_list [(make_quoted_form (unitify (char '\'')) "quote");
                 (make_quoted_form (unitify (char '`')) "quasiquote");
                 (make_quoted_form
                    (unitify (not_followed_by (char ',') (char '@')))
                    "unquote");
                 (make_quoted_form (unitify (word ",@")) "unquote-splicing")] in
    nt1 str
  and nt_sexpr str = 
    let nt1 =
      disj_list [nt_void; nt_number; nt_boolean; nt_char; nt_symbol;
                 nt_string; nt_vector; nt_list; nt_quoted_forms] in
    let nt1 = make_skipped_star nt1 in
    nt1 str;;

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
                | '\"' -> "\\\""
                | ch ->
                   if (ch < ' ')
                   then Printf.sprintf "\\x%x;" (int_of_char ch)
                   else Printf.sprintf "%c" ch)
               (list_of_string str)))
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

  let print_sexpr chan sexpr = output_string chan (string_of_sexpr sexpr);;

  let print_sexprs chan sexprs =
    output_string chan
      (Printf.sprintf "[%s]"
         (String.concat "; "
            (List.map string_of_sexpr sexprs)));;

  let sprint_sexpr _ sexpr = string_of_sexpr sexpr;;

  let sprint_sexprs chan sexprs =
    Printf.sprintf "[%s]"
      (String.concat "; "
         (List.map string_of_sexpr sexprs));;

  let scheme_sexpr_list_of_sexpr_list sexprs =
    List.fold_right (fun car cdr -> ScmPair (car, cdr)) sexprs ScmNil;;

end;; (* end of struct Reader *);;
                                                  val string_of_sexpr : sexpr -> string = <fun>
val string_of_sexpr' : string -> sexpr -> string = <fun>
#   val print_sexpr : out_channel -> sexpr -> unit = <fun>
#           val print_sexprs : out_channel -> sexpr list -> unit = <fun>
#   val sprint_sexpr : 'a -> sexpr -> string = <fun>
#         val sprint_sexprs : 'a -> sexpr list -> string = <fun>
#     val scheme_sexpr_list_of_sexpr_list : sexpr list -> sexpr = <fun>
#   Line 2, characters 0-3:
2 | end;; (* end of struct Reader *);;
    ^^^
Error: Syntax error
#  let unitify nt = pack nt (fun _ -> ());;
Line 1, characters 18-22:
1 |  let unitify nt = pack nt (fun _ -> ());;
                      ^^^^
Error: Unbound value pack
# open PC;;
#  let unitify nt = pack nt (fun _ -> ());;
val unitify : 'a PC.parser -> unit PC.parser = <fun>
#  let rec nt_whitespace str =
    const (fun ch -> ch <= ' ') str
  and nt_end_of_line_or_file str = 
    let nt1 = unitify (char '\n') in
    let nt2 = unitify nt_end_of_input inopen PC;;
    let nt1 = disj nt1 nt2 in
    nt1 str
  and nt_line_comment str =
    let nt1 = char ';' in
    let nt2 = diff nt_any nt_end_of_line_or_file in
    let nt2 = star nt2 in
    let nt1 = caten nt1 nt2 in
    let nt1 = caten nt1 nt_end_of_line_or_file in
    let nt1 = unitify nt1 in
    nt1 str
  and nt_paired_comment str = raise X_not_yet_implemented
  and nt_sexpr_comment str = raise X_not_yet_implemented
  and nt_comment str =
    disj_list
      [nt_line_comment;
       nt_paired_comment;
       nt_sexpr_comment] str;;
        Line 5, characters 47-49:
5 |     let nt2 = unitify nt_end_of_input inopen PC;;
                                                   ^^
Error: Syntax error
#                                 Line 3, characters 2-5:
3 |   and nt_line_comment str =
      ^^^
Error: Syntax error
# let rec nt_whitespace str =
    const (fun ch -> ch <= ' ') str
  and nt_end_of_line_or_file str = 
    let nt1 = unitify (char '\n') in
    let nt2 = unitify nt_end_of_input inopen PC;;
    let nt1 = disj nt1 nt2 in
    nt1 str
  and nt_line_comment str =
    let nt1 = char ';' in
    let nt2 = diff nt_any nt_end_of_line_or_file in
    let nt2 = star nt2 in
    let nt1 = caten nt1 nt2 in
    let nt1 = caten nt1 nt_end_of_line_or_file in
    let nt1 = unitify nt1 in
    nt1 str
  and nt_paired_comment str = raise X_not_yet_implemented
  and nt_sexpr_comment str = raise X_not_yet_implemented
  and nt_comment str =
    disj_list
      [nt_line_comment;
       nt_paired_comment;
       nt_sexpr_comment] str ;;
        Line 5, characters 47-49:
5 |     let nt2 = unitify nt_end_of_input inopen PC;;
                                                   ^^
Error: Syntax error
#                                 Line 3, characters 2-5:
3 |   and nt_line_comment str =
      ^^^
Error: Syntax error
#  let rec nt_whitespace str =
    const (fun ch -> ch <= ' ') str;;
  val nt_whitespace : string -> int -> char PC.parsing_result = <fun>
# nt_end_of_line_or_file str = 
    let nt1 = unitify (char '\n') in
    let nt2 = unitify nt_end_of_input inopen PC;;
    let nt1 = disj nt1 nt2 in
    nt1 str;;
    Line 3, characters 47-49:
3 |     let nt2 = unitify nt_end_of_input inopen PC;;
                                                   ^^
Error: Syntax error
#   Line 1, characters 19-22:
1 |     let nt1 = disj nt1 nt2 in
                       ^^^
Error: Unbound value nt1
# let nt_end_of_line_or_file str = 
    let nt1 = unitify (char '\n') in
    let nt2 = unitify nt_end_of_input inopen PC;;
    let nt1 = disj nt1 nt2 in
    nt1 str;;
    Line 3, characters 47-49:
3 |     let nt2 = unitify nt_end_of_input inopen PC;;
                                                   ^^
Error: Syntax error
#   Line 1, characters 19-22:
1 |     let nt1 = disj nt1 nt2 in
                       ^^^
Error: Unbound value nt1
# let nt_skip_star str =
    let nt1 = disj (unitify nt_whitespace) nt_comment in
    let nt1 = unitify (star nt1) in
    nt1 str;;
      Line 2, characters 43-53:
2 |     let nt1 = disj (unitify nt_whitespace) nt_comment in
                                               ^^^^^^^^^^
Error: Unbound value nt_comment
# let  nt_comment str =
    disj_list
      [nt_line_comment;
       nt_paired_comment;
       nt_sexpr_comment] str;;
        Line 3, characters 7-22:
3 |       [nt_line_comment;
           ^^^^^^^^^^^^^^^
Error: Unbound value nt_line_comment
# let  nt_line_comment str =
    let nt1 = char ';' in
    let nt2 = diff nt_any nt_end_of_line_or_file in
    let nt2 = star nt2 in
    let nt1 = caten nt1 nt2 in
    let nt1 = caten nt1 nt_end_of_line_or_file in
    let nt1 = unitify nt1 in
    nt1 str;;
              Line 3, characters 26-48:
3 |     let nt2 = diff nt_any nt_end_of_line_or_file in
                              ^^^^^^^^^^^^^^^^^^^^^^
Error: Unbound value nt_end_of_line_or_file
# let nt_end_of_line_or_file str = 
    let nt1 = unitify (char '\n') in
    let nt2 = unitify nt_end_of_input inopen PC;;
    let nt1 = disj nt1 nt2 in
    nt1 str;;
    Line 3, characters 47-49:
3 |     let nt2 = unitify nt_end_of_input inopen PC;;
                                                   ^^
Error: Syntax error
#   Line 1, characters 19-22:
1 |     let nt1 = disj nt1 nt2 in
                       ^^^
Error: Unbound value nt1
# let  rec nt_whitespace str =
    const (fun ch -> ch <= ' ') str
  and nt_end_of_line_or_file str = 
    let nt1 = unitify (char '\n') in
    let nt2 = unitify nt_end_of_input in
    let nt3 = disj nt1 nt2 in
    nt3 str
  and nt_line_comment str =
    let nt1 = char ';' in
    let nt2 = diff nt_any nt_end_of_line_or_file in
    let nt2 = star nt2 in
    let nt1 = caten nt1 nt2 in
    let nt1 = caten nt1 nt_end_of_line_or_file in
    let nt1 = unitify nt1 in
    nt1 str
  and nt_paired_comment str = raise X_not_yet_implemented
  and nt_sexpr_comment str = raise X_not_yet_implemented
  and nt_comment str =
    disj_list
      [nt_line_comment;
       nt_paired_comment;
       nt_sexpr_comment] str
  and nt_void str =
    let nt1 = word_ci "#void" in
    let nt1 = not_followed_by nt1 nt_symbol_char in
    let nt1 = pack nt1 (fun _ -> ScmVoid) in
    nt1 str
  and nt_skip_star str =
    let nt1 = disj (unitify nt_whitespace) nt_comment in
    let nt1 = unitify (star nt1) in
    nt1 str ;;
                                                            Line 25, characters 34-48:
25 |     let nt1 = not_followed_by nt1 nt_symbol_char in
                                       ^^^^^^^^^^^^^^
Error: Unbound value nt_symbol_char
# let rec nt_whitespace str =
    const (fun ch -> ch <= ' ') str
  and nt_end_of_line_or_file str = 
    let nt1 = unitify (char '\n') in
    let nt2 = unitify nt_end_of_input in
    let nt3 = disj nt1 nt2 in
    nt3 str
  and nt_line_comment str =
    let nt1 = char ';' in
    let nt2 = diff nt_any nt_end_of_line_or_file in
    let nt2 = star nt2 in
    let nt1 = caten nt1 nt2 in
    let nt1 = caten nt1 nt_end_of_line_or_file in
    let nt1 = unitify nt1 in
    nt1 str
  and nt_paired_comment str = raise X_not_yet_implemented
  and nt_sexpr_comment str = raise X_not_yet_implemented
  and nt_comment str =
    disj_list
      [nt_line_comment;
       nt_paired_comment;
       nt_sexpr_comment] str;;
                                          val nt_whitespace : string -> int -> char PC.parsing_result = <fun>
val nt_end_of_line_or_file : unit PC.parser = <fun>
val nt_line_comment : unit PC.parser = <fun>
val nt_paired_comment : unit PC.parser = <fun>
val nt_sexpr_comment : unit PC.parser = <fun>
val nt_comment : string -> int -> unit PC.parsing_result = <fun>
# let  nt_skip_star str =
    let nt1 = disj (unitify nt_whitespace) nt_comment in
    let nt1 = unitify (star nt1) in
    nt1 str;;
      val nt_skip_star : string -> int -> unit PC.parsing_result = <fun>
# let  make_skipped_star (nt : 'a parser) =
    let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
    let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
    nt1
  and nt_digit str = 
    let nt1 = const (fun ch -> '0' <= ch && ch <= '9' ) in
    let ascii_0 = int_of_char '0' in
    let nt2 = pack nt1 (fun ch -> (int_of_char ch) - ascii_0 ) in
nt_void str =
    let nt1 = word_ci "#void" in
    let nt1 = not_followed_by nt1 nt_symbol_char in
    let nt1 = pack nt1 (fun _ -> ScmVoid) in
    nt1 str
  and nt_skip_star str =
    let nt1 = disj (unitify nt_whitespace) nt_comment in
    let nt1 = unitify (star nt1) in
    nt1 str
  and make_skipped_star (nt : 'a parser) =
    let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
    let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
    nt1
  and nt_digit str = 
    let nt1 = const (fun ch -> '0' <= ch && ch <= '9' ) in
    let ascii_0 = int_of_char '0' in
    let nt2 = pack nt1 (fun ch -> (int_of_char ch) - ascii_0 ) in
    nt2 str    nt2 str
  and nt_hex_digit str = raise X_not_yet_implemented
  and nt_nat =
    let rec nt str =
      pack (caten nt_digit (disj nt nt_epsilon)) (function (a, s) -> a :: s) str in
      pack nt (fun s -> (List.fold_left (fun a b -> 10 * a + b) 0 s));;
                          Line 13, characters 18-26:
13 |       pack (caten nt_digit (disj nt nt_epsilon)) (function (a, s) -> a :: s) str in
                       ^^^^^^^^
Error: Unbound value nt_digit
# let nt_symbol_char str =
    let nt1 = range_ci 'a' 'z' in
    let nt1 = pack nt1 Char.lowercase_ascii in
    let nt2 = range '0' '9' in
    let nt3 = one_of "!$^*_-+=<>?/" in
    let nt1 = disj nt1 (disj nt2 nt3) in
    nt1 str;;
            val nt_symbol_char : string -> int -> char PC.parsing_result = <fun>
# let nt_void str =
    let nt1 = word_ci "#void" in
    let nt1 = not_followed_by nt1 nt_symbol_char in
    let nt1 = pack nt1 (fun _ -> ScmVoid) in
    nt1 str
  and nt_skip_star str =
    let nt1 = disj (unitify nt_whitespace) nt_comment in
    let nt1 = unitify (star nt1) in
    nt1 str
  and make_skipped_star (nt : 'a parser) =
    let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
    let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
    nt1
  and nt_digit str = 
    let nt1 = const (fun ch -> '0' <= ch && ch <= '9' ) in
    let ascii_0 = int_of_char '0' in
    let nt2 = pack nt1 (fun ch -> (int_of_char ch) - ascii_0 ) in
    nt2 str;;
                                  val nt_void : string -> int -> sexpr PC.parsing_result = <fun>
val nt_skip_star : string -> int -> unit PC.parsing_result = <fun>
val make_skipped_star : 'a PC.parser -> 'a PC.parser = <fun>
val nt_digit : string -> int -> int PC.parsing_result = <fun>
# let  nt_nat =
    let rec nt str =
      pack (caten nt_digit (disj nt nt_epsilon)) (function (a, s) -> a :: s) str in
      pack nt (fun s -> (List.fold_left (fun a b -> 10 * a + b) 0 s))
  and nt_hex_nat str = 
    let nt1 = plus nt_hex_digit in
    let nt1 = pack nt1
                (fun digits ->
                  List.fold_left
                    (fun num digit ->
                      16 * num + digit)
                    0
                    digits) in
    nt1 str;;
                          Line 6, characters 19-31:
6 |     let nt1 = plus nt_hex_digit in
                       ^^^^^^^^^^^^
Error: Unbound value nt_hex_digit
# let nt_nat =
    let rec nt str =
      pack (caten nt_digit (disj nt nt_epsilon)) (function (a, s) -> a :: s) str in
      pack nt (fun s -> (List.fold_left (fun a b -> 10 * a + b) 0 s));;
      val nt_nat : int PC.parser = <fun>
# let nt_optional_sign str =
    let nt1 = const (fun ch -> '+'== ch ) in
    let nt2  = const (fun ch-> '-'== ch ) in
    let nt3  = pack nt1 (fun ch -> true) in 
    let nt4 = pack nt2 (fun ch -> false) in
    let nt5 = disj nt3 nt4 in
    nt5 str
  and nt_int str =
    let nt1 = caten nt_optional_sign nt_nat in
    let nt1 = pack nt1
                (fun (is_positive, n) ->
                  if is_positive then n else -n) in
    nt1 str
  and nt_frac str =
    let nt1 = caten nt_int (char '/') in
    let nt1 = pack nt1 (fun (num, _) -> num) in
    let nt2 = only_if nt_nat (fun n -> n != 0) in
    let nt1 = caten nt1 nt2 in
    let nt1 = pack nt1
                (fun (num, den) ->
                  let d = gcd num den in
                  ScmRational(num / d, den / d)) in
    nt1 str
  and nt_integer_part str =
    let nt1 = plus nt_digit in
    let nt1 = pack nt1
                (fun digits ->
                  List.fold_left
                    (fun num digit -> 10.0 *. num +. (float_of_int digit))
                    0.0
                    digits) in
    nt1 str
  and nt_mantissa str =
    let nt1 = plus nt_digit in
    let nt1 = pack nt1
                (fun digits ->
                  List.fold_right
                    (fun digit num ->
                      ((float_of_int digit) +. num) /. 10.0)
                    digits
                    0.0) in
    nt1 str
  and nt_exponent str =
    let nt1 = unitify (char_ci 'e') in
    let nt2 = word "*10" in
    let nt3 = unitify (word "**") in
    let nt4 = unitify (char '^') in
    let nt3 = disj nt3 nt4 in
    let nt2 = caten nt2 nt3 in
    let nt2 = unitify nt2 in
    let nt1 = disj nt1 nt2 in
    let nt1 = caten nt1 nt_int in
    let nt1 = pack nt1 (fun (_, n) -> Float.pow 10. (float_of_int n)) in
    nt1 str
  and nt_floatA str =
    let nt1 = nt_nat in
    let nt2 = char '.' in
    let nt3 = make_maybe nt_mantissa in
    let nt4 = make_maybe nt_exponent in
    let nt5 = caten nt1 (caten nt2 ( caten nt3 nt4)) in
    nt5 str
  and nt_floatB str =
    let nt1 = char '.' in
    let nt2 = nt_mantissa in
    let nt3 = make_maybe nt_exponent in
    let nt4 = caten nt1 (caten nt2 nt3) in
    nt4 str
  and nt_floatC str = 
    let nt1 = nt_nat in
    let nt2 = nt_exponent in
    let nt3 = caten  nt1 nt2  in
    nt3 str
  and nt_float str =
    let nt1 = nt_optional_sign in
    let nt2 = nt_floatA in
    let nt3 = nt_floatB in
    let nt4 = nt_floatC in
    let nt5 = disj nt2 nt3 nt4 in
    let nt6 = caten nt1 nt5 in
    nt6 str;;
                                                                                                                                                              Line 9, characters 20-36:
9 |     let nt1 = caten nt_optional_sign nt_nat in
                        ^^^^^^^^^^^^^^^^
Error: Unbound value nt_optional_sign
Hint: If this is a recursive definition,
you should add the 'rec' keyword on line 1
# let nt_optional_sign str =
    let nt1 = const (fun ch -> '+'== ch ) in
    let nt2  = const (fun ch-> '-'== ch ) in
    let nt3  = pack nt1 (fun ch -> true) in 
    let nt4 = pack nt2 (fun ch -> false) in
    let nt5 = disj nt3 nt4 in
    nt5 str;;
            val nt_optional_sign : string -> int -> bool PC.parsing_result = <fun>
#  let nt_optional_sign str =
    let nt1 = const (fun ch -> '+'== ch ) in
    let nt2  = const (fun ch-> '-'== ch ) in
    let nt3  = pack nt1 (fun ch -> true) in 
    let nt4 = pack nt2 (fun ch -> false) in
    let nt5 = disj nt3 nt4 in
    nt5 str
  and nt_int str =
    let nt1 = caten nt_optional_sign nt_nat in
    let nt1 = pack nt1
                (fun (is_positive, n) ->
                  if is_positive then n else -n) in
    nt1 str
  and nt_frac str =
    let nt1 = caten nt_int (char '/') in
    let nt1 = pack nt1 (fun (num, _) -> num) in
    let nt2 = only_if nt_nat (fun n -> n != 0) in
    let nt1 = caten nt1 nt2 in
    let nt1 = pack nt1
                (fun (num, den) ->
                  let d = gcd num den in
                  ScmRational(num / d, den / d)) in
    nt1 str
  and nt_integer_part str =
    let nt1 = plus nt_digit in
    let nt1 = pack nt1
                (fun digits ->
                  List.fold_left
                    (fun num digit -> 10.0 *. num +. (float_of_int digit))
                    0.0
                    digits) in
    nt1 str
  and nt_mantissa str =
    let nt1 = plus nt_digit in
    let nt1 = pack nt1
                (fun digits ->
                  List.fold_right
                    (fun digit num ->
                      ((float_of_int digit) +. num) /. 10.0)
                    digits
                    0.0) in
    nt1 str
  and nt_exponent str =
    let nt1 = unitify (char_ci 'e') in
    let nt2 = word "*10" in
    let nt3 = unitify (word "**") in
    let nt4 = unitify (char '^') in
    let nt3 = disj nt3 nt4 in
    let nt2 = caten nt2 nt3 in
    let nt2 = unitify nt2 in
    let nt1 = disj nt1 nt2 in
    let nt1 = caten nt1 nt_int in
    let nt1 = pack nt1 (fun (_, n) -> Float.pow 10. (float_of_int n)) in
    nt1 str
  and nt_floatA str =
    let nt1 = nt_nat in
    let nt2 = char '.' in
    let nt3 = make_maybe nt_mantissa in
    let nt4 = make_maybe nt_exponent in
    let nt5 = caten nt1 (caten nt2 ( caten nt3 nt4)) in
    nt5 str
  and nt_floatB str =
    let nt1 = char '.' in
    let nt2 = nt_mantissa in
    let nt3 = make_maybe nt_exponent in
    let nt4 = caten nt1 (caten nt2 nt3) in
    nt4 str
  and nt_floatC str = 
    let nt1 = nt_nat in
    let nt2 = nt_exponent in
    let nt3 = caten  nt1 nt2  in
    nt3 str
  and nt_float str =
    let nt1 = nt_optional_sign in
    let nt2 = nt_floatA in
    let nt3 = nt_floatB in
    let nt4 = nt_floatC in
    let nt5 = disj nt2 nt3 nt4 in
    let nt6 = caten nt1 nt5 in
    nt6 str;;
                                                                                                                                                              Line 15, characters 20-26:
15 |     let nt1 = caten nt_int (char '/') in
                         ^^^^^^
Error: Unbound value nt_int
Hint: Did you mean nt_any or nt_nat?
Hint: If this is a recursive definition,
you should add the 'rec' keyword on line 1
# 
  and nt_int str =
    let nt1 = caten nt_optional_sign nt_nat in
    let nt1 = pack nt1
                (fun (is_positive, n) ->
                  if is_positive then n else -n) in
    nt1 str
  and nt_frac str =
    let nt1 = caten nt_int (char '/') in
    let nt1 = pack nt1 (fun (num, _) -> num) in
    let nt2 = only_if nt_nat (fun n -> n != 0) in
    let nt1 = caten nt1 nt2 in
    let nt1 = pack nt1
                (fun (num, den) ->
                  let d = gcd num den in
                  ScmRational(num / d, den / d)) in
    nt1 str
  and nt_integer_part str =
    let nt1 = plus nt_digit in
    let nt1 = pack nt1
                (fun digits ->
                  List.fold_left
                    (fun num digit -> 10.0 *. num +. (float_of_int digit))
                    0.0
                    digits) in
    nt1 str
  and nt_mantissa str =
    let nt1 = plus nt_digit in
    let nt1 = pack nt1
                (fun digits ->
                  List.fold_right
                    (fun digit num ->
                      ((float_of_int digit) +. num) /. 10.0)
                    digits
                    0.0) in
    nt1 str
  and nt_exponent str =
    let nt1 = unitify (char_ci 'e') in
    let nt2 = word "*10" in
    let nt3 = unitify (word "**") in
    let nt4 = unitify (char '^') in
    let nt3 = disj nt3 nt4 in
    let nt2 = caten nt2 nt3 in
    let nt2 = unitify nt2 in
    let nt1 = disj nt1 nt2 in
    let nt1 = caten nt1 nt_int in
    let nt1 = pack nt1 (fun (_, n) -> Float.pow 10. (float_of_int n)) in
    nt1 str
  and nt_floatA str =
    let nt1 = nt_nat in
    let nt2 = char '.' in
    let nt3 = make_maybe nt_mantissa in
    let nt4 = make_maybe nt_exponent in
    let nt5 = caten nt1 (caten nt2 ( caten nt3 nt4)) in
    nt5 str
  and nt_floatB str =
    let nt1 = char '.' in
    let nt2 = nt_mantissa in
    let nt3 = make_maybe nt_exponent in
    let nt4 = caten nt1 (caten nt2 nt3) in
    nt4 str
  and nt_floatC str = 
    let nt1 = nt_nat in
    let nt2 = nt_exponent in
    let nt3 = caten  nt1 nt2  in
    nt3 str
  and nt_float str =
    let nt1 = nt_optional_sign in
    let nt2 = nt_floatA in
    let nt3 = nt_floatB in
    let nt4 = nt_floatC in
    let nt5 = disj nt2 nt3 nt4 in
    let nt6 = caten nt1 nt5 in
    nt6 str;;
                                                                                                                                                  Line 2, characters 2-5:
2 |   and nt_int str =
      ^^^
Error: Syntax error
# let nt_int str =
    let nt1 = caten nt_optional_sign nt_nat in
    let nt1 = pack nt1
                (fun (is_positive, n) ->
                  if is_positive then n else -n) in
    nt1 str;;
          val nt_int : string -> int -> int PC.parsing_result = <fun>
# let  nt_frac str =
    let nt1 = caten nt_int (char '/') in
    let nt1 = pack nt1 (fun (num, _) -> num) in
    let nt2 = only_if nt_nat (fun n -> n != 0) in
    let nt1 = caten nt1 nt2 in
    let nt1 = pack nt1
                (fun (num, den) ->
                  let d = gcd num den in
                  ScmRational(num / d, den / d)) in
    nt1 str;;
                  val nt_frac : string -> int -> scm_number PC.parsing_result = <fun>
# let  nt_integer_part str =
    let nt1 = plus nt_digit in
    let nt1 = pack nt1
                (fun digits ->
                  List.fold_left
                    (fun num digit -> 10.0 *. num +. (float_of_int digit))
                    0.0
                    digits) in
    nt1 str;;
                val nt_integer_part : string -> int -> float PC.parsing_result = <fun>
# let  nt_mantissa str =
    let nt1 = plus nt_digit in
    let nt1 = pack nt1
                (fun digits ->
                  List.fold_right
                    (fun digit num ->
                      ((float_of_int digit) +. num) /. 10.0)
                    digits
                    0.0) in
    nt1 str
  and nt_exponent str =
    let nt1 = unitify (char_ci 'e') in
    let nt2 = word "*10" in
    let nt3 = unitify (word "**") in
    let nt4 = unitify (char '^') in
    let nt3 = disj nt3 nt4 in
    let nt2 = caten nt2 nt3 in
    let nt2 = unitify nt2 in
    let nt1 = disj nt1 nt2 in
    let nt1 = caten nt1 nt_int in
    let nt1 = pack nt1 (fun (_, n) -> Float.pow 10. (float_of_int n)) in
    nt1 str;;
                                          val nt_mantissa : string -> int -> float PC.parsing_result = <fun>
val nt_exponent : string -> int -> float PC.parsing_result = <fun>
# let  nt_floatA str =
    let nt1 = nt_nat in
    let nt2 = char '.' in
    let nt3 = make_maybe nt_mantissa in
    let nt4 = make_maybe nt_exponent in
    let nt5 = caten nt1 (caten nt2 ( caten nt3 nt4)) in
    nt5 str
  and nt_floatB str =
    let nt1 = char '.' in
    let nt2 = nt_mantissa in
    let nt3 = make_maybe nt_exponent in
    let nt4 = caten nt1 (caten nt2 nt3) in
    nt4 str
  and nt_floatC str = 
    let nt1 = nt_nat in
    let nt2 = nt_exponent in
    let nt3 = caten  nt1 nt2  in
    nt3 str;;
                                  Line 4, characters 14-24:
4 |     let nt3 = make_maybe nt_mantissa in
                  ^^^^^^^^^^
Error: Unbound value make_maybe
Hint: Did you mean make_range?
#  let  make_maybe nt none_value =
  pack (maybe nt)
    (function
     | None -> none_value
     | Some(x) -> x);;
        val make_maybe : 'a PC.parser -> 'a -> 'a PC.parser = <fun>
# let  nt_floatA str =
    let nt1 = nt_nat in
    let nt2 = char '.' in
    let nt3 = make_maybe nt_mantissa in
    let nt4 = make_maybe nt_exponent in
    let nt5 = caten nt1 (caten nt2 ( caten nt3 nt4)) in
    nt5 str
  and nt_floatB str =
    let nt1 = char '.' in
    let nt2 = nt_mantissa in
    let nt3 = make_maybe nt_exponent in
    let nt4 = caten nt1 (caten nt2 nt3) in
    nt4 str
  and nt_floatC str = 
    let nt1 = nt_nat in
    let nt2 = nt_exponent in
    let nt3 = caten  nt1 nt2  in
    nt3 str
  and nt_float str =
    let nt1 = nt_optional_sign in
    let nt2 = nt_floatA in
    let nt3 = nt_floatB in
    let nt4 = nt_floatC in
    let nt5 = disj nt2 nt3 nt4 in
    let nt6 = caten nt1 nt5 in
    nt6 str;;
                                                  Line 6, characters 43-46:
6 |     let nt5 = caten nt1 (caten nt2 ( caten nt3 nt4)) in
                                               ^^^
Error: This expression has type float -> float PC.parser
       but an expression was expected of type
         'a PC.parser = string -> int -> 'a PC.parsing_result
       Type float is not compatible with type string 
# let nt_floatA str =
    let nt1 = nt_nat in
    let nt2 = word "." in
    let nt3 = make_maybe nt_mantissa in
    let nt4 = make_maybe nt_exponent in
    let nt5 = caten nt1 (caten nt2 ( caten nt3 nt4)) in
    nt5 str;;
            Line 6, characters 43-46:
6 |     let nt5 = caten nt1 (caten nt2 ( caten nt3 nt4)) in
                                               ^^^
Error: This expression has type float -> float PC.parser
       but an expression was expected of type
         'a PC.parser = string -> int -> 'a PC.parsing_result
       Type float is not compatible with type string 
# let  nt_mantissa str =
    let nt1 = plus nt_digit in
    let nt1 = pack nt1
                (fun digits ->
                  List.fold_right
                    (fun digit num ->
                      ((float_of_int digit) +. num) /. 10.0)
                    digits
                    0.0) in
    nt1 str;;
                  val nt_mantissa : string -> int -> float PC.parsing_result = <fun>
# let  nt_floatA str =
    pack ( nt_floatA str =
    pack (caten nt_int_string mantissa) (fun (n,m) -> n^mcaten nt_int_string mantissa) (fun (n,m) -> n^m;;
  Line 2, characters 57-59:
2 |     pack (caten nt_int_string mantissa) (fun (n,m) -> n^m;;
                                                             ^^
Error: Syntax error: ')' expected
Line 2, characters 40-41:
2 |     pack (caten nt_int_string mantissa) (fun (n,m) -> n^m;;
                                            ^
  This '(' might be unmatched
#  nt_floatA str =
    pack (caten nt_int_string mantissa) (fun (n,m) -> n^m) ;;
  Line 1, characters 1-10:
1 |  nt_floatA str =
     ^^^^^^^^^
Error: Unbound value nt_floatA
# let  nt_floatA str =
    let nt1 = nt_nat in
    let nt2 = word "." in
    let nt3 = make_maybe nt_mantissa in
    let nt4 = make_maybe nt_exponent in
    let nt5 = caten nt1 nt2 in
    let nt6 = caten nt5 nt3 in
    let nt7 = caten nt6 nt4 in 
    nt7 str;;
                Line 7, characters 24-27:
7 |     let nt6 = caten nt5 nt3 in
                            ^^^
Error: This expression has type float -> float PC.parser
       but an expression was expected of type
         'a PC.parser = string -> int -> 'a PC.parsing_result
       Type float is not compatible with type string 
# let nt_floatA str =
    let nt1 = nt_int in
    let nt2 = word "." in
    let nt3 = make_maybe nt_mantissa in
    let nt4 = make_maybe nt_exponent in
    let nt5 = caten nt1 nt2 in
    let nt6 = caten nt5 nt3 in
    let nt7 = caten nt6 nt4 in 
    nt7 str;;
                Line 7, characters 24-27:
7 |     let nt6 = caten nt5 nt3 in
                            ^^^
Error: This expression has type float -> float PC.parser
       but an expression was expected of type
         'a PC.parser = string -> int -> 'a PC.parsing_result
       Type float is not compatible with type string 
# let  nt_int str =
    let nt1 = caten nt_optional_sign nt_nat in
    let nt1 = pack nt1
                (fun (is_positive, n) ->
                  if is_positive then n else -n) in
    nt1 str;;
          val nt_int : string -> int -> int PC.parsing_result = <fun>
# let nt_floatA str =
    let nt1 = string_of_sexpr nt_int in
    let nt2 = word "." in
    let nt3 = make_maybe nt_mantissa in
    let nt4 = make_maybe nt_exponent in
    let nt5 = caten nt1 nt2 in
    let nt6 = caten nt5 nt3 in
    let nt7 = caten nt6 nt4 in 
    nt7 str;;
                Line 2, characters 30-36:
2 |     let nt1 = string_of_sexpr nt_int in
                                  ^^^^^^
Error: This expression has type string -> int -> int PC.parsing_result
       but an expression was expected of type sexpr
# let nt_floatA str =
    let nt1 = nt_integer_part in
    let nt2 = word "." in
    let nt3 = make_maybe nt_mantissa in
    let nt4 = make_maybe nt_exponent in
    let nt5 = caten nt1 nt2 in
    let nt6 = caten nt5 nt3 in
    let nt7 = caten nt6 nt4 in 
    nt7 str;;
                Line 7, characters 24-27:
7 |     let nt6 = caten nt5 nt3 in
                            ^^^
Error: This expression has type float -> float PC.parser
       but an expression was expected of type
         'a PC.parser = string -> int -> 'a PC.parsing_result
       Type float is not compatible with type string 
# nt_nat;;
- : int PC.parser = <fun>
# nt_integer_part;;
- : string -> int -> float PC.parsing_result = <fun>
# let nt_nat str =
    let nt1 = plus nt_digit in
    let nt1 = pack nt1
                (fun digits ->
                  List.fold_left
                    (fun num digit -> 10.0 *. num +. (float_of_int digit))
                    0.0
                    digits) in
    nt1 str;;
                val nt_nat : string -> int -> float PC.parsing_result = <fun>
#  nt_int str =
    let nt1 = caten nt_optional_sign nt_nat in
    let nt1 = pack nt1
                (fun (is_positive, n) ->
                  if is_positive then n else -n) in
    nt1 str;;
          Line 1, characters 8-11:
1 |  nt_int str =
            ^^^
Error: Unbound value str
Hint: Did you mean star?
# let  nt_int str =
    let nt1 = caten nt_optional_sign nt_nat in
    let nt1 = pack nt1
                (fun (is_positive, n) ->
                  if is_positive then n else -n) in
    nt1 str;;
          Line 5, characters 46-47:
5 |                   if is_positive then n else -n) in
                                                  ^
Error: This expression has type float but an expression was expected of type
         int
# let nt_integer_part str =
    let nt1 = plus nt_digit in
    let nt1 = pack nt1
                (fun digits ->
                  List.fold_left
                    (fun num digit -> 10.0 *. num +. (float_of_int digit))
                    0.0
                    digits) in
    nt1 str;;
                val nt_integer_part : string -> int -> float PC.parsing_result = <fun>
# nt_integer_part "345.56" 0;;
- : float PC.parsing_result = {index_from = 0; index_to = 3; found = 345.}
# let  nt_floatA str =
    let nt1 = (nt_integer_part).found in
    let nt2 = word "." in
    let nt3 = make_maybe nt_mantissa in
    let nt4 = make_maybe nt_exponent in
    let nt5 = caten nt1 nt2 in
    let nt6 = caten nt5 nt3 in
    let nt7 = caten nt6 nt4 in 
    nt7 str;;
                Line 2, characters 14-31:
2 |     let nt1 = (nt_integer_part).found in
                  ^^^^^^^^^^^^^^^^^
Error: This expression has type string -> int -> float PC.parsing_result
       which is not a record type.
# let  nt_floatA str =
    let nt1 = (nt_integer_part).found() in
    let nt2 = word "." in
    let nt3 = make_maybe nt_mantissa in
    let nt4 = make_maybe nt_exponent in
    let nt5 = caten nt1 nt2 in
    let nt6 = caten nt5 nt3 in
    let nt7 = caten nt6 nt4 in 
    nt7 str;;
                Line 2, characters 14-31:
2 |     let nt1 = (nt_integer_part).found() in
                  ^^^^^^^^^^^^^^^^^
Error: This expression has type string -> int -> float PC.parsing_result
       which is not a record type.
# let  nt_floatA str =
    let nt1 = nt_integer_part  in
    let nt2 = word "." in
    let nt3 = make_maybe nt_mantissa in
    let nt4 = make_maybe nt_exponent in
    let nt5 = caten nt1 nt2 in
    let nt6 = caten nt5 nt3 in
    let nt7 = caten nt6 nt4 in 
    nt7 str;;
                Line 7, characters 24-27:
7 |     let nt6 = caten nt5 nt3 in
                            ^^^
Error: This expression has type float -> float PC.parser
       but an expression was expected of type
         'a PC.parser = string -> int -> 'a PC.parsing_result
       Type float is not compatible with type string 
# let nt_floatA str =
    let nt1 = string_of_int nt_integer_part  in
    let nt2 = word "." in
    let nt3 = make_maybe nt_mantissa in
    let nt4 = make_maybe nt_exponent in
    let nt5 = caten nt1 nt2 in
    let nt6 = caten nt5 nt3 in
    let nt7 = caten nt6 nt4 in 
    nt7 str;;
                Line 2, characters 28-43:
2 |     let nt1 = string_of_int nt_integer_part  in
                                ^^^^^^^^^^^^^^^
Error: This expression has type string -> int -> float PC.parsing_result
       but an expression was expected of type int
# let nt_floatA str =
    let nt1 = string_of_float nt_integer_part  in
    let nt2 = word "." in
    let nt3 = make_maybe nt_mantissa in
    let nt4 = make_maybe nt_exponent in
    let nt5 = caten nt1 nt2 in
    let nt6 = caten nt5 nt3 in
    let nt7 = caten nt6 nt4 in 
    nt7 str;;
                Line 2, characters 30-45:
2 |     let nt1 = string_of_float nt_integer_part  in
                                  ^^^^^^^^^^^^^^^
Error: This expression has type string -> int -> float PC.parsing_result
       but an expression was expected of type float
# let 1 str
  and nt_floatA str =
    let nt1 = nt_integer_part  in
    let nt9 = pack nt1 (fun digit -> string_of_float digit )
    let nt2 = word "." in
    let nt3 = make_maybe nt_mantissa in
    let nt4 = make_maybe nt_exponent in
    let nt5 = caten nt9 nt2 in
    let nt6 = caten nt5 nt3 in
    let nt7 = caten nt6 nt4 in 
    nt7 str;;
                    Line 1, characters 6-9:
1 | let 1 str
          ^^^
Error: Syntax error
# let  nt_floatA str =
    let nt1 = nt_integer_part  in
    let nt9 = pack nt1 (fun digit -> string_of_float digit )
    let nt2 = word "." in
    let nt3 = make_maybe nt_mantissa in
    let nt4 = make_maybe nt_exponent in
    let nt5 = caten nt9 nt2 in
    let nt6 = caten nt5 nt3 in
    let nt7 = caten nt6 nt4 in 
    nt7 str;;
                  Line 4, characters 4-7:
4 |     let nt2 = word "." in
        ^^^
Error: Syntax error
# let  nt_floatA str =
    let nt1 = nt_integer_part  in
    let nt9 = pack nt1 (fun digit -> string_of_float digit ) in
    let nt2 = word "." in
    let nt3 = make_maybe nt_mantissa in
    let nt4 = make_maybe nt_exponent in
    let nt5 = caten nt9 nt2 in
    let nt6 = caten nt5 nt3 in
    let nt7 = caten nt6 nt4 in 
    nt7 str;;
                  Line 8, characters 24-27:
8 |     let nt6 = caten nt5 nt3 in
                            ^^^
Error: This expression has type float -> float PC.parser
       but an expression was expected of type
         'a PC.parser = string -> int -> 'a PC.parsing_result
       Type float is not compatible with type string 
# let  nt_floatA str =
    let nt1 = nt_integer_part  in
    let nt9 = pack nt1 (fun digit -> string_of_float digit ) in
    let nt2 = word "." in
    let nt8 = pack nt2 (fun ch -> "." ) in
    let nt3 = make_maybe nt_mantissa in
    let nt4 = make_maybe nt_exponent in
    let nt5 = caten nt9 nt8 in
    let nt6 = caten nt5 nt3 in
    let nt7 = caten nt6 nt4 in 
    nt7 str;;
                    Line 9, characters 24-27:
9 |     let nt6 = caten nt5 nt3 in
                            ^^^
Error: This expression has type float -> float PC.parser
       but an expression was expected of type
         'a PC.parser = string -> int -> 'a PC.parsing_result
       Type float is not compatible with type string 
# let  nt_floatA str =
    let nt1 = nt_integer_part  in
    let nt9 = pack nt1 (fun digit -> string_of_float digit ) in
    let nt2 = word "." in
    let nt3 = make_maybe nt_mantissa in
    let nt8 = pack nt3 (fun str -> string_of_float str) in
    let nt4 = make_maybe nt_exponent in
    let nt5 = caten nt9 nt2 in
    let nt6 = caten nt5 nt8 in
    let nt7 = caten nt6 nt4 in 
    nt7 str;;
                    Line 6, characters 19-22:
6 |     let nt8 = pack nt3 (fun str -> string_of_float str) in
                       ^^^
Error: This expression has type float -> float PC.parser
       but an expression was expected of type
         'a PC.parser = string -> int -> 'a PC.parsing_result
       Type float is not compatible with type string 
# let nt_floatA str =
    let nt1 = nt_integer_part  in
    let nt9 = pack nt1 (fun digit -> string_of_float digit ) in
    let nt2 = char '.' in
    let nt3 = make_maybe nt_mantissa in
    let nt8 = pack nt3 (fun str -> string_of_float str) in
    let nt4 = make_maybe nt_exponent in
    let nt5 = caten nt9 nt2 in
    let nt6 = caten nt5 nt8 in
    let nt7 = caten nt6 nt4 in 
    nt7 str;;
                    Line 6, characters 19-22:
6 |     let nt8 = pack nt3 (fun str -> string_of_float str) in
                       ^^^
Error: This expression has type float -> float PC.parser
       but an expression was expected of type
         'a PC.parser = string -> int -> 'a PC.parsing_result
       Type float is not compatible with type string 
# clear;;
Line 1, characters 0-5:
1 | clear;;
    ^^^^^
Error: Unbound value clear
Hint: Did you mean char?
# nt_mantissa "12.465" 0;;
- : float PC.parsing_result = {index_from = 0; index_to = 2; found = 0.12}
# let nt_floatA str =
    let nt1 = nt_integer_part  in
    let nt2 = char '.' in
    let nt3 = make_maybe nt_mantissa in
    let nt8 = pack nt3 (fun res -> string_of_float res.found) in
    let nt4 = make_maybe nt_exponent in
    let nt5 = caten nt1 nt2 in
    let nt6 = caten nt5 nt8 in
    let nt7 = caten nt6 nt4 in 
    nt7 str;;
                  Line 5, characters 19-22:
5 |     let nt8 = pack nt3 (fun res -> string_of_float res.found) in
                       ^^^
Error: This expression has type float -> float PC.parser
       but an expression was expected of type
         'a PC.parser = string -> int -> 'a PC.parsing_result
       Type float is not compatible with type string 
# nt_floatA str =
    let nt1 = nt_integer_part  in
    let nt2 = char '.' in
    let nt3 = make_maybe nt_mantissa in
    let nt4 = make_maybe nt_exponent in
    let nt5 = caten nt1 nt2 in
    let nt6 = caten nt5 nt3 in
    let nt7 = caten nt6 nt4 in 
    nt7 str;;
                Line 1, characters 0-9:
1 | nt_floatA str =
    ^^^^^^^^^
Error: Unbound value nt_floatA
# let nt_floatA str =
    let nt1 = nt_integer_part  in
    let nt2 = char '.' in
    let nt3 = make_maybe nt_mantissa in
    let nt4 = make_maybe nt_exponent in
    let nt5 = caten nt1 nt2 in
    let nt6 = caten nt5 nt3 in
    let nt7 = caten nt6 nt4 in 
    nt7 str;;
                Line 7, characters 24-27:
7 |     let nt6 = caten nt5 nt3 in
                            ^^^
Error: This expression has type float -> float PC.parser
       but an expression was expected of type
         'a PC.parser = string -> int -> 'a PC.parsing_result
       Type float is not compatible with type string 
# let nt_test = pack nt_mantissa (func ch -> string_of_float (ch.found));;
Line 1, characters 40-42:
1 | let nt_test = pack nt_mantissa (func ch -> string_of_float (ch.found));;
                                            ^^
Error: Syntax error: ')' expected
Line 1, characters 31-32:
1 | let nt_test = pack nt_mantissa (func ch -> string_of_float (ch.found));;
                                   ^
  This '(' might be unmatched
#  let nt_test = pack nt_mantissa (func ch -> string_of_float ch.found);;
Line 1, characters 41-43:
1 |  let nt_test = pack nt_mantissa (func ch -> string_of_float ch.found);;
                                             ^^
Error: Syntax error: ')' expected
Line 1, characters 32-33:
1 |  let nt_test = pack nt_mantissa (func ch -> string_of_float ch.found);;
                                    ^
  This '(' might be unmatched
# nt_mantissa "12.00" 0;;
- : float PC.parsing_result = {index_from = 0; index_to = 2; found = 0.12}
# nt_exponent "12.00" 0;;
Exception: PC.X_no_match.
# nt_integer_part "12.56" 0;;
- : float PC.parsing_result = {index_from = 0; index_to = 2; found = 12.}
# let nt_floatA str =
    let nt1 = nt_integer_part  in
    (*let nt2 = char '.' in *)
    let nt3 = make_maybe nt_mantissa in
    let nt4 = make_maybe nt_exponent in
    (*let nt5 = caten nt1 nt2 in *)
    let nt6 = caten nt1 nt3 in
    let nt7 = caten nt6 nt4 in 
    nt7 str;;
                Line 7, characters 24-27:
7 |     let nt6 = caten nt1 nt3 in
                            ^^^
Error: This expression has type float -> float PC.parser
       but an expression was expected of type
         'a PC.parser = string -> int -> 'a PC.parsing_result
       Type float is not compatible with type string 
# let nt_floatA str =
    let nt1 = nt_integer_part  in
    (*let nt2 = char '.' in *)
    let nt3 = maybe nt_mantissa in
    let nt4 = maybe nt_exponent in
    (*let nt5 = caten nt1 nt2 in *)
    let nt6 = caten nt1 nt3 in
    let nt7 = caten nt6 nt4 in 
    nt7 str;;
                val nt_floatA :
  string -> int -> ((float * float option) * float option) PC.parsing_result =
  <fun>
# let  nt_floatA str =
    let nt1 = nt_integer_part  in
    let nt2 = char '.' in 
    let nt3 = maybe nt_mantissa in
    let nt4 = maybe nt_exponent in
    let nt5 = caten nt1 nt2 in 
    let nt6 = caten nt1 nt3 in
    let nt7 = caten nt6 nt4 in 
    nt7 str;;
                Line 6, characters 8-11:
6 |     let nt5 = caten nt1 nt2 in 
            ^^^
Warning 26 [unused-var]: unused variable nt5.
val nt_floatA :
  string -> int -> ((float * float option) * float option) PC.parsing_result =
  <fun>
# let  nt_floatA str =
    let nt1 = nt_integer_part  in
    let nt2 = char '.' in 
    let nt3 = maybe nt_mantissa in
    let nt4 = maybe nt_exponent in
    let nt5 = caten nt1 nt2 in 
    let nt6 = caten nt5 nt3 in
    let nt7 = caten nt6 nt4 in 
    nt7 str;;
                val nt_floatA :
  string ->
  int -> (((float * char) * float option) * float option) PC.parsing_result =
  <fun>
# nt_floatA "12.45" 0;;
- : (((float * char) * float option) * float option) PC.parsing_result =
{index_from = 0; index_to = 5; found = (((12., '.'), Some 0.45), None)}
# let fla = pack (caten nt_int_string mantissa) (fun (n,m) -> n^m);;
Line 1, characters 22-35:
1 | let fla = pack (caten nt_int_string mantissa) (fun (n,m) -> n^m);;
                          ^^^^^^^^^^^^^
Error: Unbound value nt_int_string
Hint: Did you mean print_string?
# let nt_int_string = pack nt_int (fun (e) -> string_of_int e);;
val nt_int_string : string PC.parser = <fun>
# let fla = pack (caten nt_int_string mantissa) (fun (n,m) -> n^m);;
Line 1, characters 36-44:
1 | let fla = pack (caten nt_int_string mantissa) (fun (n,m) -> n^m);;
                                        ^^^^^^^^
Error: Unbound value mantissa
Hint: Did you mean nt_mantissa?
# let fla = pack (caten nt_int_string nt_mantissa) (fun (n,m) -> n^m);;
Line 1, characters 65-66:
1 | let fla = pack (caten nt_int_string nt_mantissa) (fun (n,m) -> n^m);;
                                                                     ^
Error: This expression has type float but an expression was expected of type
         string
# let mantissa = pack (caten char_dot mantissa) (fun(_,e) -> e);;
Line 1, characters 27-35:
1 | let mantissa = pack (caten char_dot mantissa) (fun(_,e) -> e);;
                               ^^^^^^^^
Error: Unbound value char_dot
Hint: Did you mean char_ci?
# let char_dot = char '.';;
val char_dot : char PC.parser = <fun>
# let mantissa = pack (caten char_dot mantissa) (fun(_,e) -> e);;
Line 1, characters 36-44:
1 | let mantissa = pack (caten char_dot mantissa) (fun(_,e) -> e);;
                                        ^^^^^^^^
Error: Unbound value mantissa
Hint: Did you mean nt_mantissa?
# let mantissa = pack (maybe nt_mantissa) (fun (e)->
    match e with
    | Some(e) -> "."^e
    | None -> ""
    ) ;;
        Line 3, characters 21-22:
3 |     | Some(e) -> "."^e
                         ^
Error: This expression has type float but an expression was expected of type
         string
# nt_integer_part "12.45" ;;
- : int -> float PC.parsing_result = <fun>
# nt_integer_part "12.45" 0;;
- : float PC.parsing_result = {index_from = 0; index_to = 2; found = 12.}
# let nt11 = pack nt1  (fun s ->
                  match s with
                  | Some(e) -> "."^e
                  | None -> "" );;
      Line 1, characters 16-19:
1 | let nt11 = pack nt1  (fun s ->
                    ^^^
Error: Unbound value nt1
# let nt1 str = nt_integer_part str ;;
val nt1 : string -> int -> float PC.parsing_result = <fun>
# nt1 "12.45" 0;;
- : float PC.parsing_result = {index_from = 0; index_to = 2; found = 12.}
# let nt11 = pack nt1  (fun s ->
                  match s with
                  | Some(e) -> "."^e
                  | None -> "" );;
      Line 3, characters 20-27:
3 |                   | Some(e) -> "."^e
                        ^^^^^^^
Error: This pattern matches values of type 'a option
       but a pattern was expected which matches values of type float
#  let nt11 = pack nt1  (fun s ->
                  match s with
                  |{index_from; index_to; found = Some(e)} -> "."^e
		  |None -> "" ;;
      Line 4, characters 16-18:
4 | 		  |None -> "" ;;
    		              ^^
Error: Syntax error: ')' expected
Line 1, characters 22-23:
1 |  let nt11 = pack nt1  (fun s ->
                          ^
  This '(' might be unmatched
#   let nt11 = pack nt1  (fun s ->
                  match s with
                  |{index_from; index_to; found = Some(e)} -> "."^e
		  |None -> "" );;
      Line 3, characters 19-58:
3 |                   |{index_from; index_to; found = Some(e)} -> "."^e
                       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: This pattern matches values of type 'a option PC.parsing_result
       but a pattern was expected which matches values of type float
#   let nt11 = 
            ( fun str index ->  match (nt1 str index) with
                  |{index_from; index_to; found = Some(e)} -> "."^e
		  |None -> "" );;
      Line 3, characters 50-57:
3 |                   |{index_from; index_to; found = Some(e)} -> "."^e
                                                      ^^^^^^^
Error: This pattern matches values of type 'a option
       but a pattern was expected which matches values of type float
#  let nt11 = 
            ( fun str index ->  match (nt1 str index) with
                  |{index_from; index_to; found = e} -> "."^e
		  |None -> "" );;
      Line 4, characters 5-9:
4 | 		  |None -> "" );;
    		   ^^^^
Error: This pattern should not be a constructor, the expected type is
       float PC.parsing_result
#  let nt11 = 
            ( fun str index ->  match (nt1 str index) with
                  |{index_from; index_to; found = Some(e)} -> "."^e );;
    Line 3, characters 50-57:
3 |                   |{index_from; index_to; found = Some(e)} -> "."^e );;
                                                      ^^^^^^^
Error: This pattern matches values of type 'a option
       but a pattern was expected which matches values of type float
#  let nt11 = 
            ( fun str index ->  match (nt1 str index) with
                  |{index_from; index_to; found = e} -> "."^e );;
    Line 3, characters 60-61:
3 |                   |{index_from; index_to; found = e} -> "."^e );;
                                                                ^
Error: This expression has type float but an expression was expected of type
         string
# let nt11 = pack nt1 (fun s -> let {index_from; index_to; found = e} = (nt1 s 0) in
				e^".");;
  Line 1, characters 75-76:
1 | let nt11 = pack nt1 (fun s -> let {index_from; index_to; found = e} = (nt1 s 0) in
                                                                               ^
Error: This expression has type float but an expression was expected of type
         string
#  let nt11 = pack nt1 (fun fl -> (string_of_float fl)^".");;
val nt11 : string PC.parser = <fun>
# nt11 "12.45" 0;;
- : string PC.parsing_result = {index_from = 0; index_to = 2; found = "12.."}
# let nt11 = pack nt1 (fun fl ->"."^(string_of_float fl));;
val nt11 : string PC.parser = <fun>
# nt11 "12.45" 0;;
- : string PC.parsing_result = {index_from = 0; index_to = 2; found = ".12."}
# let  nt_floatA str =
    let ch = char '.' in
    let nt1 = pack (caten nt_integer_part ch) (fun (n,_) -> n ) in
    let nt2 = pack (maybe nt_mantissa) (fun man ->
                  match man with
                  |None ->0.0
                  |Some(e) -> e) in
    let nt3 = pack( caten nt1 nt2 ) ( fun (i,m) -> i +. m ) in
    let nt4 =  pack (maybe nt_exponent) (fun e ->
                  match e with
                  |None ->1.0
                  |Some(e) -> e) in
    let nt5 = pack (caten nt3 nt4) (fun (f ,e) -> f *. e) in
    nt5 str;;
                          val nt_floatA : string -> int -> float PC.parsing_result = <fun>
# nt_floatA "12.45" 0;;
- : float PC.parsing_result = {index_from = 0; index_to = 5; found = 12.45}
# nt_float "12.45e^2" 0;;
Line 1, characters 0-8:
1 | nt_float "12.45e^2" 0;;
    ^^^^^^^^
Error: Unbound value nt_float
Hint: Did you mean nt_floatA?
# nt_floatA "12.45e2" 0;;
- : float PC.parsing_result = {index_from = 0; index_to = 5; found = 12.45}
# nt_floatA "1.234*10^1" 0;;
- : float PC.parsing_result = {index_from = 0; index_to = 5; found = 1.234}
# nt_floatA "1.234e1" 0;;
- : float PC.parsing_result = {index_from = 0; index_to = 5; found = 1.234}
# nt_floatA "1.234e+1" 0;;
- : float PC.parsing_result = {index_from = 0; index_to = 8; found = 12.34}
# let nt_floatAA str =
    let nt1 = char '.' in
    let nt2 = nt_integer_part in
    let nt3 = nt_mantissa in
    let nt4 = nt_exponent in
    let nt5 = caten nt2 nt1 in
    let nt6 = pack nt5 (fun (ipart, dot) -> ipart);;
            Line 7, characters 50-52:
7 |     let nt6 = pack nt5 (fun (ipart, dot) -> ipart);;
                                                      ^^
Error: Syntax error
# let nt_floatAA str =
    let nt1 = char '.' in
    let nt2 = nt_integer_part in
    let nt3 = nt_mantissa in
    let nt4 = nt_exponent in
    let nt5 = caten nt2 nt1 in
    let nt6 = pack nt5 (fun (ipart, dot) -> ipart) in
    nt6 str;;
              Line 4, characters 8-11:
4 |     let nt3 = nt_mantissa in
            ^^^
Warning 26 [unused-var]: unused variable nt3.
Line 5, characters 8-11:
5 |     let nt4 = nt_exponent in
            ^^^
Warning 26 [unused-var]: unused variable nt4.
val nt_floatAA : string -> int -> float PC.parsing_result = <fun>
# nt_floatAA "12.45" 0;;

- : float PC.parsing_result = {index_from = 0; index_to = 3; found = 12.}
#   nt_floatAA "1245" 0;;
Exception: PC.X_no_match.
#  let nt_floatAAA str =
    let nt1 = char '.' in
    let nt2 = nt_integer_part in
    let nt3 = nt_mantissa in
    let nt4 = nt_exponent in
    let nt5 = caten nt2 nt1 in
    let nt6 = pack nt5 (fun (ipart, _) -> ipart) in
    nt6 str;;
              Line 4, characters 8-11:
4 |     let nt3 = nt_mantissa in
            ^^^
Warning 26 [unused-var]: unused variable nt3.
Line 5, characters 8-11:
5 |     let nt4 = nt_exponent in
            ^^^
Warning 26 [unused-var]: unused variable nt4.
val nt_floatAAA : string -> int -> float PC.parsing_result = <fun>
# nt_floatAAA "1234" 0;;
Exleception: PC.X_no_match.
# let nt_floatA str =
    let nt1 = char '.' in
    let nt2 = nt_integer_part in
    let nt3 = maybe nt_mantissa in
    let nt33 = pack nt3 (fun mvalue -> match mvalue with
                                       | Some(e) -> e
                                       | None -> 0.0
                 ) in
    let nt4 = maybe nt_exponent in
    let nt44 = pack nt4 (fun evalue -> match evalue with
                                       | Some(e) -> e
                                       | None -> 1.0
                 ) in
    let nt5 = caten nt2 nt1 in
    let nt6 = pack nt5 (fun (ipart, dot) -> ipart) in
    let nt7 = caten nt6 nt33 in
    let nt8 = pack nt7 (fun (ipart, mvalue) -> ipart +. mvalue) in
    let nt9 = caten nt8 nt44 in
    let nt10 = pack nt9 (fun (fpart, evalue) -> fpart *. evalue) in
    nt10 str;;
                                      val nt_floatA : string -> int -> float PC.parsing_result = <fun>
# nt_floatA "1.234e+1" 0;;
				      
- : float PC.parsing_result = {index_from = 0; index_to = 8; found = 12.34}
#   let  nt_floatB str =
    let nt1 = char '.' in
    let nt2 = nt_mantissa in
    let nt3 = pack nt2 (fun mvalue -> match mvalue with
                                       | Some(e) -> e
                                       | None -> 0.0
                 ) in
    let nt4 = maybe nt_exponent in
    let nt44 = pack nt4 (fun evalue -> match evalue with
                                       | Some(e) -> e
                                       | None -> 1.0
                 ) in
    let nt5 = caten nt1 nt2 in
    let nt6 = pack nt5 (fun (ipart, dot) -> ipart) in
    let nt7 = caten nt6 nt33 in
    let nt8 = pack nt7 (fun (ipart, mvalue) -> ipart +. mvalue) in
    let nt9 = caten nt8 nt44 in
    let nt10 = pack nt9 (fun (fpart, evalue) -> fpart *. evalue) in
    nt10 str;;
                                    Line 6, characters 41-48:
6 |                                        | Some(e) -> e
                                             ^^^^^^^
Error: This pattern matches values of type 'a option
       but a pattern was expected which matches values of type float
# let nt_floatB str =
    let nt1 = char '.' in
    let nt2 = nt_mantissa in
    let nt3 = pack nt2 (fun mvalue -> match mvalue with
                                       | Some(e) -> e   ) in
    let nt4 = maybe nt_exponent in
    let nt44 = pack nt4 (fun evalue -> match evalue with
                                       | Some(e) -> e
                                       | None -> 1.0
                 ) in
    let nt5 = caten nt1 nt2 in
    let nt6 = pack nt5 (fun (ipart, dot) -> ipart) in
    let nt7 = caten nt6 nt33 in
    let nt8 = pack nt7 (fun (ipart, mvalue) -> ipart +. mvalue) in
    let nt9 = caten nt8 nt44 in
    let nt10 = pack nt9 (fun (fpart, evalue) -> fpart *. evalue) in
    nt10 str;;
                                Line 5, characters 41-48:
5 |                                        | Some(e) -> e   ) in
                                             ^^^^^^^
Error: This pattern matches values of type 'a option
       but a pattern was expected which matches values of type float
# let  nt_floatB str =
    let nt1 = char '.' in
    let nt2 = nt_mantissa in
    let nt4 = maybe nt_exponent in
    let nt44 = pack nt4 (fun evalue -> match evalue with
                                       | Some(e) -> e
                                       | None -> 1.0
                 ) in
    let nt5 = caten nt1 nt2 in
    let nt6 = pack nt5 (fun (dot, mpart) -> mpart) in
    let nt9 = caten nt6 nt44 in
    let nt10 = pack nt9 (fun (fpart, evalue) -> fpart *. evalue) in
    nt10 str;;
                        val nt_floatB : string -> int -> float PC.parsing_result = <fun>
# nt_floatB ".45" 0;;
- : float PC.parsing_result = {index_from = 0; index_to = 3; found = 0.45}
# nt_floatB ".45e1" 0;;
- : float PC.parsing_result = {index_from = 0; index_to = 3; found = 0.45}
# nt_floatB ".45e3" 0;;
- : float PC.parsing_result = {index_from = 0; index_to = 3; found = 0.45}
# nt_floatB ".45e+2" 0;;
- : float PC.parsing_result = {index_from = 0; index_to = 6; found = 45.}
#  let nt_floatC str =
       let nt1 = nt_integer_part in
       let nt2 = nt_exponent in
       let nt3 = caten nt1 nt2 in
       let nt4 = pack nt3 (fun (ipart, evalue) -> ipart *. evalue ) in
       nt4 str;;
          val nt_floatC : string -> int -> float PC.parsing_result = <fun>
# nt_floatC "123e+2" 0;;
- : float PC.parsing_result = {index_from = 0; index_to = 6; found = 12300.}
# let nt_float str =
    let nt1 = nt_optional_sign in
    let nt2 = nt_floatA in
    let nt3 = nt_floatB in
    let nt4 = nt_floatC in
    let nt5 = disj nt2 nt3 nt4 in
    let nt6 = caten nt1 nt5 in
    nt6 str;;
              Line 6, characters 27-30:
6 |     let nt5 = disj nt2 nt3 nt4 in
                               ^^^
Error: This expression has type string -> int -> float PC.parsing_result
       but an expression was expected of type string
# let  nt_float str =
    let nt1 = nt_optional_sign in
    let nt2 = nt_floatA in
    let nt3 = nt_floatB in
    let nt4 = nt_floatC in
    let nt5 = disj nt2 nt3 in
    let nt55 = disj nt5 nt4 in
    let nt6 = caten nt1 nt55 in
    nt6 str;;
                val nt_float : string -> int -> (bool * float) PC.parsing_result = <fun>
# nt_float "1234.45e+2" 0;;
Exception: PC.X_no_match.
# let  nt_optional_sign str =
    let nt1 = const (fun ch -> '+'== ch ) in
    let nt2  = const (fun ch-> '-'== ch ) in
    let nt3  = pack nt1 (fun ch -> true) in 
    let nt4 = pack nt2 (fun ch -> false) in
    let nt5 = disj nt3 nt4 in
    let nt6 = maybe nt5 in
    nt6 str;;
              val nt_optional_sign : string -> int -> bool option PC.parsing_result = <fun>
# let  nt_float str =
    let nt1 = nt_optional_sign in
    let nt11 = pack nt1 (fun svalue ->
                   match svalue with
                   | some(e) -> e
                   | None -> true
    let nt2 = nt_floatA in
    let nt3 = nt_floatB in
    let nt4 = nt_floatC in
    let nt5 = disj nt2 nt3 in
    let nt55 = disj nt5 nt4 in
    let nt6 = caten nt11 nt55 in
    let nt7 = pack nt6 (fun (b, value) ->
                  match b with
                  |true -> value
                  |false -> -1.0 *. value ) in 
    nt7 str;;
                                Line 5, characters 25-26:
5 |                    | some(e) -> e
                             ^
Error: Syntax error
# let  nt_float str =
    let nt1 = nt_optional_sign in
    let nt11 = pack nt1 (fun svalue ->
                   match svalue with
                   | Some(e) -> e
                   | None -> true
    let nt2 = nt_floatA in
    let nt3 = nt_floatB in
    let nt4 = nt_floatC in
    let nt5 = disj nt2 nt3 in
    let nt55 = disj nt5 nt4 in
    let nt6 = caten nt11 nt55 in
    let nt7 = pack nt6 (fun (b, value) ->
                  match b with
                  |true -> value
                  |false -> -1.0 *. value ) in 
    nt7 str;;
                                Line 7, characters 4-7:
7 |     let nt2 = nt_floatA in
        ^^^
Error: Syntax error: ')' expected
Line 3, characters 24-25:
3 |     let nt11 = pack nt1 (fun svalue ->
                            ^
  This '(' might be unmatched
# let  nt_float str =
    let nt1 = nt_optional_sign in
    let nt11 = pack nt1 (fun svalue ->
                   match svalue with
                   | Some(e) -> e
                   | None -> true ) in
    let nt2 = nt_floatA in
    let nt3 = nt_floatB in
    let nt4 = nt_floatC in
    let nt5 = disj nt2 nt3 in
    let nt55 = disj nt5 nt4 in
    let nt6 = caten nt11 nt55 in
    let nt7 = pack nt6 (fun (b, value) ->
                  match b with
                  |true -> value
                  |false -> -1.0 *. value ) in 
    nt7 str;;
                                val nt_float : string -> int -> float PC.parsing_result = <fun>
# nt_float "1324.45e+2" 0;;
- : float PC.parsing_result =
{index_from = 0; index_to = 10; found = 132445.}
# nt_float "-1234.45e+2" 0;;
- : float PC.parsing_result =
{index_from = 0; index_to = 11; found = -123445.}
# 
