(* Sum type to encode efficiently polynomial expressions *)
type pExp =
  | Term of int*int (*
      First int is the constant
      Second int is the power of x 
      10  -> Term(10,0)
      2x -> Term(2,1)
      3x^20 -> Term(3, 20)
    *)
  | Plus of pExp list
  (*
    List of terms added
    Plus([Term(2,1); Term(1,0)])
  *)
  | Times of pExp list (* List of terms multiplied *)
  | Divides of pExp list
;;



(* 
  Compute degree of a polynomial expression.

  Hint 1: Degree of Term(n,m) is m
  Hint 2: Degree of Plus[...] is the max of the degree of args
  Hint 3: Degree of Times[...] is the sum of the degree of args 
*)
let rec degree (_e:pExp): int =
  match _e with
    | Term(n, m) -> m
    | Plus(l) -> get_degree_plus l 0
    | Times(l) -> get_degree_times l 0
    | Divides(l) -> 0

and get_degree_plus (el:pExp list) (hi:int) : int = 
  match el with
    | [] -> hi
    | hd::tl ->
      let current = degree hd in
      if(current > hi ) then
        get_degree_plus tl current
      else
        get_degree_plus tl hi

and get_degree_times (el:pExp list) (hi:int) : int = 
  match el with
    | [] -> hi
    | hd::tl ->
      let current = degree hd in
      let hi = current + hi in
        get_degree_times tl hi
;;

(* 
  Comparison function useful for sorting of Plus[..] args 
  to "normalize them". This way, terms that need to be reduced
  show up one after another.
  *)
let compare (e1: pExp) (e2: pExp) : int =
  if( degree e1 > degree e2 ) then -1
  else if(degree e1 < degree e2) then 1
  else 0
;;

let sort_by_degree (p: pExp list) : pExp list =
  List.sort compare p
;;



(*
  Function to traslate betwen AST expressions
  to pExp expressions

  TODO make Times - Times instead of flattening now
*)
let rec pow_to_times (p: pExp) (li: pExp list) (cnt: int) (exp: int) : pExp =
  let newList = p::li in
  let cnt = cnt + 1 in
  if (cnt < exp) then
    pow_to_times p newList cnt exp
  else
    Times(newList)
;;

let rec from_expr (_e: Expr.expr) : pExp =
    match _e with
      | Num(i) -> Term(i, 0)
      | Var(c) -> Term(1, 1)
      | Add(e1, e2) ->
        let t1 = from_expr e1 in
        let t2 = from_expr e2 in
          let l = t1::t2::[] in
          let l = sort_by_degree l in
            Plus(l)
      | Sub(e1, e2) ->
        let t1 = from_expr e1 in
        let t2 = from_expr e2 in
        let n = Term(-1, 0) in
          let n1 = Times(n::t2::[]) in
            let l = t1::n1::[] in
            let l = sort_by_degree l in
            Plus(l)
      | Mul(e1, e2) ->
        let t1 = from_expr e1 in
        let t2 = from_expr e2 in
          let l = t1::t2::[] in
          let l = sort_by_degree l in
            Times(l)
      | Div(e1, e2) ->
        let t1 = from_expr e1 in
        let t2 = from_expr e2 in
          Divides(t1::t2::[])
      | Pow(e1, i) ->
        (
        match e1 with
          | Num(ni) ->
            let fn = float_of_int ni in
            let fi = float_of_int i in
              let f = fn ** fi in
                let f = int_of_float f in
                  Term(f, 0)
          | Var(c) -> Term(1, i)
          | _ ->
            let t = from_expr e1 in
              pow_to_times t [] 0 i
        )
      | Pos(e1) ->
        let n = Term(1, 0) in
        let t = from_expr e1 in
          Times(n::t::[])
      | Neg(e1) -> 
        let n = Term(-1, 0) in
        let t = from_expr e1 in
          Times(n::t::[])
;;


(* Print a pExpr nicely 
  Term(3,0) -> 3
  Term(5,1) -> 5x 
  Term(4,2) -> 4x^2
  Plus... -> () + () 
  Times ... -> ()() .. ()

  Hint 1: Print () around elements that are not Term() 
  Hint 2: Recurse on the elements of Plus[..] or Times[..]
*)
(* TODO - Loop times and plus so dont have () arround every single one, low priority *)
let rec print_pExp (_e: pExp): unit =
  match _e with
    | Term(m, n) ->
      if(n > 1 && m > 1) then 
        Printf.printf "%dx^%d" m n
      else if (n > 1) then
        Printf.printf "x^%d" n
      else if(n > 0 && m > 1) && m > 1 then
        Printf.printf "%dx" m
      else if (n > 0) then
      Printf.printf "x"
      else
        Printf.printf "%d" m
    | Plus(l) ->
      (
      match l with
        | h::t::li ->
          Printf.printf("(");
          print_pExp h;
          Printf.printf("+");
          print_pExp t;
          (
          match li with
            | [] -> Printf.printf(")");
            | _ ->
              Printf.printf("+");
              let t = Plus(li) in
                print_pExp t;
          )
        | h::[] ->
          print_pExp h;
        | [] ->
          Printf.printf "";
      )
    | Times(l) ->
      (
        match l with
          | h::t::li ->
            Printf.printf("(");
            print_pExp h;
            Printf.printf("*");
            print_pExp t;
            (
            match li with
            | [] -> Printf.printf(")");
            | _ ->
              Printf.printf("*");
              let t = Plus(li) in
                print_pExp t;
            )
        | h::[] ->
          Printf.printf("*");
          print_pExp h;
        | [] ->
          Printf.printf "";
      )
    | Divides(l) ->
      (
        match l with
        | h::t::li ->
        Printf.printf("(");
        print_pExp h;
        Printf.printf(")");
        Printf.printf("/");
        Printf.printf("(");
        print_pExp t;
        Printf.printf(")");
        let p = Plus(li) in
          print_pExp p;
        | h::[] ->
          Printf.printf("/");
          print_pExp h;
        | [] ->
          Printf.printf "";
      )
;;



(* 
  Function to simplify (one pass) pExpr

  n1 x^m1 * n2 x^m2 -> n1*n2 x^(m1+m2)
  Term(n1,m1)*Term(n2,m2) -> Term(n1*n2,m1+m2)

  Hint 1: Keep terms in Plus[...] sorted
  Hint 2: flatten plus, i.e. Plus[ Plus[..], ..] => Plus[..]
  Hint 3: flatten times, i.e. times of times is times
  Hint 4: Accumulate terms. Term(n1,m)+Term(n2,m) => Term(n1+n2,m)
          Term(n1, m1)*Term(n2,m2) => Term(n1*n2, m1+m2)
  Hint 5: Use distributivity, i.e. Times[Plus[..],] => Plus[Times[..],]
    i.e. Times[Plus[Term(1,1); Term(2,2)]; Term(3,3)] 
      => Plus[Times[Term(1,1); Term(3,3)]; Times[Term(2,2); Term(3,3)]]
      => Plus[Term(2,3); Term(6,5)]
  Hint 6: Find other situations that can arise
*)

let rec distributive_term (t:pExp) (p:pExp list) (l: pExp list): pExp list=
  match p with
  | hd::tl ->
    let ti = Times(t::hd::[]) in
      let l = ti::l in
        distributive_term t tl l
  | [] -> l
  ;;

let rec inner_loop (p: pExp) (el: pExp list) (l: pExp list) : pExp list =
  match el with
  | [] -> l
  | hd::tl ->
    let t = Times(p::hd::[]) in
    let l = t::l in
      inner_loop p tl l
;;

let rec distributive_plus (el1:pExp list) (el2:pExp list) (l: pExp list): pExp list=
  match el1 with
  | [] -> l
  | hd::tl ->
    let l1 = [] in
    let t = inner_loop hd el2 l1 in
    let l = t@l in
      distributive_plus tl el2 l
  ;;

(* NOTE: The labels for all names go Outer expression type - Head type - second element type*)
let rec simplify1 (e:pExp): pExp =
    match e with
      | Term(i1, i2) -> e

      | Plus(el) -> 
        (
          match el with
            | hd::tl::li ->
              (
                match hd with
                  | Term(m1, n1) ->
                    (
                      match tl with
                        | Term(m2, n2) -> (* Plus - Term - Term *)
                          if(n1 = n2) then
                            let t = Term(m1 + m2, n1) in
                            (
                              match li with
                               | [] -> t
                               | _ ->
                                  let l = t::li in
                                  let l = sort_by_degree l in
                                    Plus(l)
                            )
                          else
                            (
                            match li with
                              | [] -> e
                              | hd2::tl2 ->
                                let p = Plus(tl::hd2::tl2) in
                                let s = simplify1 p in
                                (
                                match s with
                                  | Plus(el) ->
                                      Plus(hd::el) (* Flatten *)
                                  | _ -> Plus(hd::s::[])
                                )
                            )
                        | Plus(el) -> (* Plus - Term - Plus *) (* Flatten *)
                            let l = hd::el@li in
                            let l = sort_by_degree l in
                              Plus(l)
                        | Times(el) -> (* Plus - Term - Times *) (* Simplify tail and put into plus list *)
                          let tl = simplify1 tl in
                          let l = hd::tl::li in
                          let l = sort_by_degree l in
                            Plus(l)
                        | Divides(el) -> e (* Plus - Term - Divide *) (* TODO *)
                    )

                  | Plus(el) ->
                    (
                    match tl with
                      | Term(m, n) -> (* Plus - Plus - Term *) (* Flatten *)
                        let l = el@tl::li in
                        let l = sort_by_degree l in
                          Plus(l)
                      | Plus(el2) -> (* Plus - Plus - Plus *) (* Flatten *)
                        let l = el@el2@li in
                        let l = sort_by_degree l in
                          Plus(l)
                      | Times(el2) -> (* Plus - Plus - Times*) (* Simplify times and flatten*)
                        let tl = simplify1 tl in
                        let l = el@tl::li in
                        let l = sort_by_degree l in
                          Plus(l)
                      | Divides(el) -> e (* Plus - Plus - Divide *) (* TODO *)
                    )

                  | Times(el) ->
                    (
                      match tl with
                        | Term(m, n) -> (* Plus - Times - Term *) (* Simplify times *)
                          let hd = simplify1 hd in
                          let l = hd::tl::li in
                          let l = sort_by_degree l in
                            Plus(l)
                        | Plus(el2) -> (* Plus - Times - Plus *) (* Simplify times and flatten*)
                          let hd = simplify1 hd in
                          let l = hd::el2@li in
                          let l = sort_by_degree l in
                            Plus(l)
                        | Times(el2) -> (* Plus - Times - Times *) (* Simplify both times *)
                          let hd = simplify1 hd in
                          let tl = simplify1 tl in
                          let l = hd::tl::li in
                          let l = sort_by_degree l in
                            Plus(l)
                        | Divides(el) -> e (* Plus - Times - Divide *) (* TODO *)
                    )

                  | Divides(el) -> e (* Times - Times - Divide *) (* TODO *)
              )
            | _ -> e
        )




      | Times(el) ->
        (
        match el with
          | hd::tl::li ->
            (
            match hd with
              | Term(m1, n1) ->
                (
                  match tl with
                    | Term(m2, n2) -> (* Times - Term - Term *) (* Multiply terms, return single term or times list *)
                      let t = Term(m1 * m2, n1 + n2) in
                      (
                        match li with
                          | [] -> t
                          | _ -> Times(t::li)
                      )
                    | Plus(el) -> (* Times - Term - Plus  *) (* Expand distributive_term *)
                        let l = [] in
                        let c = distributive_term hd el l in
                        let c = sort_by_degree c in
                          let p = Plus(c) in
                          (
                            match li with
                            | [] -> p
                            | _ -> Times(p::li)
                          )
                    | Times(el) -> (* Times - Term - Times *) (* Flatten *)
                        Times(hd::el@li)
                    | Divides(el) -> e (* Times - Term - Divide *) (* TODO *)
                )
              | Plus(el) ->
                (
                match tl with
                  | Term(m, n) -> (* Times - Plus -Term *) (* Expand distributive_term *)
                      let l = [] in
                      let c = distributive_term tl el l in
                      let c = sort_by_degree c in
                        let p = Plus(c) in
                        (
                          match li with
                          | [] -> p
                          | _ -> Times(p::li)
                        )
                  | Plus(el2) -> (* Times - Plus - Plus *) (* Expand distibutive_plus *)
                      let l = [] in
                      let l = distributive_plus el el2 l in
                      let l = sort_by_degree l in
                        let p = Plus(l) in
                        (
                          match li with
                          | [] -> p
                          | _ -> Times(p::li)
                        )
                  | Times(el) -> (* Times - Plus - Times *) (* Simplify Times *)
                      let tl = simplify1 tl in
                        Times(hd::tl::li)
                  | Divides(el) -> e (* Times - Plus - Divide *) (* TODO *)
                )

              | Times(el) ->
                (
                match tl with
                  | Term(m, n) -> (* Times - Times - Term *) (* Flatten *)
                      Times(el@tl::li)
                  | Plus(el) -> (* Times - Times - Plus *) (* Simplify Times *)
                      let hd = simplify1 hd in
                      Times(hd::tl::li)
                  | Times(el2) -> (* Times - Times - Times *) (* Flatten *)
                      Times(el@el2@li)
                  | Divides(el) -> e (* Times - Times - Divide *) (* TODO *)
                )
              | Divides(el) -> e (* Times - Times - Divide *) (* TODO *)
            )
          | _ -> e
        )



      | Divides(el) -> e
;;



(* 
  Compute if two pExp are the same 
  Make sure this code works before you work on simplify1  
*)
let equal_pExp (_e1: pExp) (_e2: pExp) :bool =
  if(_e1 = _e2) then
    true
  else
    false
;;



(* Fixed point version of simplify1 
  i.e. Apply simplify1 until no 
  progress is made
*)    
let rec simplify (e:pExp): pExp =
    print_pExp e;
    Printf.printf("\n");
    let rE = simplify1(e) in
      print_pExp rE;
      Printf.printf("\n");
      if (equal_pExp e rE) then
        e
      else
        simplify(rE)
;;
