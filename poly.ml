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
;;



(*
  Function to traslate betwen AST expressions
  to pExp expressions
*)
let rec pow_to_times (p: pExp) (l: pExp list) (cnt: int) (exp: int) : pExp =
  let newList = p::l in
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
            Plus(l)
      | Sub(e1, e2) ->
        let t1 = from_expr e1 in
        let t2 = from_expr e2 in
        let n = Term(-1, 0) in
          let n1 = Times(n::t2::[]) in
            Plus(t1::n1::[])
      | Mul(e1, e2) ->
        let t1 = from_expr e1 in
        let t2 = from_expr e2 in
          let l = t1::t2::[] in
            Times(l)
      | Pow(e1, i) ->
        (
        match e1 with
          | Num(ni) ->
            let fn = float_of_int ni in
            let fi = float_of_int i in
              let f = fn ** fi in
                let i = int_of_float f in
                  Term(i, 0)
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



(* 
  Compute degree of a polynomial expression.

  Hint 1: Degree of Term(n,m) is m
  Hint 2: Degree of Plus[...] is the max of the degree of args
  Hint 3: Degree of Times[...] is the sum of the degree of args 
*)
(* TODO *)
let degree (_e:pExp): int =
  match _e with
    | Term(n, m) -> m
    | Plus(l) -> 0
    | Times(l) -> 0
;;



(* 
  Comparison function useful for sorting of Plus[..] args 
  to "normalize them". This way, terms that need to be reduced
  show up one after another.
  *)
let compare (e1: pExp) (e2: pExp) : bool =
  degree e1 > degree e2
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
(* TODO - Loop times and plus so dont have () arround every single one, low priority*)
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
        | h::t::[] ->
          Printf.printf("(");
          print_pExp h;
          Printf.printf("+");
          print_pExp t;
          Printf.printf(")");
        | _ -> Printf.printf "";
      )
    | Times(l) ->
      (
        match l with
          | h::t::[] ->
            Printf.printf("(");
            print_pExp h;
            Printf.printf("*");
            print_pExp t;
            Printf.printf(")");
          | _ -> Printf.printf ""
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
                        | Term(m2, n2) -> (* Plus - Term - Term *) (* If terms are same exp add, otherwise return plus list, if no more in plus list return term, else return list *)
                          if(n1 = n2) then
                            let t = Term(m1 + m2, n1) in
                            (
                              match li with
                               | [] -> t
                               | _ -> Plus(t::li)
                            )
                          else
                            Plus(hd::tl::li) (* Figure out how to go to next ones in cant*)
                        | Plus(el) -> (* Plus - Term - Plus *) (* Flatten *)
                            let newList = hd::el@li in
                              Plus(newList)
                        | Times(el) -> (* Plus - Term - Times *) (* Simplify tail and put into plus list *)
                          let tl = simplify1 tl in
                          let e2 = Plus(hd::tl::li) in
                            simplify1 e2
                    )

                  | Plus(el) ->
                    (
                    match tl with
                      | Term(m, n) -> (* Plus - Plus - Term *) (* Flatten - FIX*)
                        let newList = el@tl::li in
                          Plus(newList)
                      | Plus(el2) -> (* Plus - Plus - Plus *)
                        Plus(el@el2@li)
                      | Times(el2) -> (* Plus - Plus - Times*) (* Simplify times*)
                        let tl = simplify1 tl in
                          Plus(hd::tl::li)
                    )

                  | Times(el) ->
                    (
                      match tl with
                        | Term(m, n) -> (* Plus - Times - Term : (4*x)+x *)
                          let hd = simplify1 hd in
                            Plus(hd::tl::li)
                        | Plus(el2) -> (* Plus - Times - Plus *)
                          let hd = simplify1 hd in
                            Plus(hd::el2@li)
                        | Times(el2) -> (* Plus - Times - Times *)
                          let hd = simplify1 hd in
                          let tl = simplify1 tl in
                            Plus(hd::tl::li)
                    )
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
                    | Term(m2, n2) -> (* Times - Term - Term : 4x * 6 *)
                      let t = Term(m1 * m2, n1 + n2) in
                      (
                        match li with
                          | [] -> t
                          | _ -> Times(t::li)
                      )
                    | Plus(el) -> (* Times - Term - Plus : 4x * (3 + 5x) *) (* TODO - Must expand commutative *)
                      let p = Plus(el) in
                      let s = simplify1 p in
                      let e2 = Times(hd::s::li) in
                        simplify1 e2
                    | Times(el) -> (* Times - Term - Times : 4x^2 * (4 * 5x) *) (* Simplify tail and recurse, TODO - flatten *)
                      let p = Times(el) in
                      let s = simplify1 p in
                      let e2 = Times(hd::s::li) in
                        simplify1 e2
                )
              | Plus(el) ->
              let hd = simplify1 hd in
              let e2 = Times(hd::tl::li) in
                simplify1 e2
                (*match tl with
                  | Term(m, n)::[] -> (* Times - Plus -Term : (4+5x) * 3x *) (* TODO - Must expand commutative *)
                  | Plus(el)::[] -> (* Times - Plus - Plus : (5 +3x)*(2+x+3x^2) *)
                  | Times(el)::[] -> (* Times - Plus - Times : (4+x)*(4*x^2) *)*)
              | Times(el) ->
                let hd = simplify1 hd in
                let e2 = Times(hd::tl::li) in
                  simplify1 e2
            )
          | _ -> e
        )
;;



(* 
  Compute if two pExp are the same 
  Make sure this code works before you work on simplify1  
*)
(* TODO - test*)
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
    let rE = simplify1(e) in
      print_pExp rE;
      if (equal_pExp e rE) then
        e
      else
        simplify(rE)
;;




