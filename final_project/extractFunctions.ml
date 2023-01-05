(* >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>> Start of extracted code from Reader.ml!!!!!!!!!!!!!!!!!!!!!! *)
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

(* >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>> END of extracted code from Reader.ml!!!!!!!!!!!!!!!!!!!!!! *)

(* >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>> Start of extracted code from tp_sa.ml!!!!!!!!!!!!!!!!!!!!!! *)
let rec sexpr_of_expr = function
| ScmConst(ScmVoid) -> ScmVoid
| ScmConst((ScmBoolean _) as sexpr) -> sexpr
| ScmConst((ScmChar _) as sexpr) -> sexpr
| ScmConst((ScmString _) as sexpr) -> sexpr
| ScmConst((ScmNumber _) as sexpr) -> sexpr
| ScmConst((ScmSymbol _) as sexpr) ->
   ScmPair (ScmSymbol "quote", ScmPair (sexpr, ScmNil))
| ScmConst(ScmNil as sexpr) ->
   ScmPair (ScmSymbol "quote", ScmPair (sexpr, ScmNil))
| ScmConst((ScmVector _) as sexpr) ->
   ScmPair (ScmSymbol "quote", ScmPair (sexpr, ScmNil))  
| ScmVarGet(Var var) -> ScmSymbol var
| ScmIf(test, dit, ScmConst ScmVoid) ->
   let test = sexpr_of_expr test in
   let dit = sexpr_of_expr dit in
   ScmPair (ScmSymbol "if", ScmPair (test, ScmPair (dit, ScmNil)))
| ScmIf(e1, e2, ScmConst (ScmBoolean false)) ->
   let e1 = sexpr_of_expr e1 in
   (match (sexpr_of_expr e2) with
    | ScmPair (ScmSymbol "and", exprs) ->
       ScmPair (ScmSymbol "and", ScmPair(e1, exprs))
    | e2 -> ScmPair (ScmSymbol "and", ScmPair (e1, ScmPair (e2, ScmNil))))
| ScmIf(test, dit, dif) ->
   let test = sexpr_of_expr test in
   let dit = sexpr_of_expr dit in
   let dif = sexpr_of_expr dif in
   ScmPair
     (ScmSymbol "if", ScmPair (test, ScmPair (dit, ScmPair (dif, ScmNil))))
| ScmOr ([]) -> ScmBoolean false
| ScmOr ([expr]) -> sexpr_of_expr expr
| ScmOr (exprs) ->
 ScmPair(ScmSymbol "or" , Reader.scheme_sexpr_list_of_sexpr_list(List.map sexpr_of_expr exprs))
| ScmSeq([]) -> ScmVoid
| ScmSeq([expr]) -> sexpr_of_expr expr
| ScmSeq(exprs) ->
   ScmPair(ScmSymbol "begin", 
           scheme_sexpr_list_of_sexpr_list
             (List.map sexpr_of_expr exprs))
| ScmVarSet(Var var, expr) ->
   let var = ScmSymbol var in
   let expr = sexpr_of_expr expr in
   ScmPair (ScmSymbol "set!", ScmPair (var, ScmPair (expr, ScmNil)))
| ScmVarDef(Var var, expr) ->
   let var = ScmSymbol var in
   let expr = sexpr_of_expr expr in
   ScmPair (ScmSymbol "define", ScmPair (var, ScmPair (expr, ScmNil)))
| ScmLambda(params, Simple, expr) ->
   let params = scheme_sexpr_list_of_sexpr_list
                  (List.map (fun str -> ScmSymbol str) params) in
   let expr = sexpr_of_expr expr in
   ScmPair (ScmSymbol "lambda",
            ScmPair (params,
                     ScmPair (expr, ScmNil)))
| ScmLambda([], Opt opt, expr) ->
   let expr = sexpr_of_expr expr in
   let opt = ScmSymbol opt in
   ScmPair
     (ScmSymbol "lambda",
      ScmPair (opt, ScmPair (expr, ScmNil)))
| ScmLambda(params, Opt opt, expr) ->
   let expr = sexpr_of_expr expr in
   let opt = ScmSymbol opt in
   let params = List.fold_right
                  (fun param sexpr -> ScmPair(ScmSymbol param, sexpr))
                  params
                  opt in
   ScmPair
     (ScmSymbol "lambda", ScmPair (params, ScmPair (expr, ScmNil)))
| ScmApplic (ScmLambda (params, Simple, expr), args) ->
   let ribs =
     scheme_sexpr_list_of_sexpr_list
       (List.map2
          (fun param arg -> ScmPair (ScmSymbol param, ScmPair (arg, ScmNil)))
          params
          (List.map sexpr_of_expr args)) in
   let expr = sexpr_of_expr expr in
   ScmPair
     (ScmSymbol "let",
      ScmPair (ribs,
               ScmPair (expr, ScmNil)))
| ScmApplic (proc, args) ->
   let proc = sexpr_of_expr proc in
   let args =
     scheme_sexpr_list_of_sexpr_list
       (List.map sexpr_of_expr args) in
   ScmPair (proc, args)
| _ -> raise (X_syntax "Unknown form");;

let string_of_expr expr =
Printf.sprintf "%a" sprint_sexpr (sexpr_of_expr expr);;

let print_expr chan expr =
output_string chan
  (string_of_expr expr);;

let print_exprs chan exprs =
output_string chan
  (Printf.sprintf "[%s]"
     (String.concat "; "
        (List.map string_of_expr exprs)));;

let sprint_expr _ expr = string_of_expr expr;;

let sprint_exprs chan exprs =
Printf.sprintf "[%s]"
  (String.concat "; "
     (List.map string_of_expr exprs));;

(* >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>> END of extracted code from tp_sa.ml!!!!!!!!!!!!!!!!!!!!!! *)

  