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
          | Num(ni) -> Term(0, 0) (* Make exponent of ni *)
          | Var(c) -> Term(1, i)
          | _ -> Term(0, 0) (* Turn into Times e1 i times *)
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
let rec simplify1 (e:pExp): pExp =
    match e with
      | Term(i1, i2) -> e

      | Plus(el) -> 
        (
          match el with
            | hd::tl ->
              (
                match hd with
                  | Term(m1, n1) ->
                    (
                      match tl with
                        | Term(m2, n2)::[] ->
                          if(n1 = n2) then
                            Term(m1 + m2, n1)
                          else
                            Plus(hd::tl)
                        | Plus(el)::[] ->
                          let p = Plus(el) in
                          let tl = simplify1 p in
                          let e2 = Plus(hd::tl::[]) in
                            simplify1 e2
                        | Times(el)::[] ->
                          let p = Times(el) in
                          let tl = simplify1 p in
                          let e2 = Plus(hd::tl::[]) in
                            simplify1 e2
                        | [] -> hd
                    )
                  | Plus(el) -> let p = Plus(el) in simplify1 p (* handle *)
                  | Times(el) -> let p = Plus(el) in simplify1 p (* handle *)
              )
            | _ -> e
        )

      | Times(el) ->
        (
        match el with
          | hd::tl ->
            (
            match hd with
              | Term(m1, n1) ->
                (
                  match tl with
                    | Term(m2, n2)::[] ->
                      Term(m1 * m2, n1 + n2)
                    | Plus(el)::[] ->
                      let p = Plus(el) in
                      let s = simplify1 p in
                      let e2 = Times(hd::s::[]) in
                        simplify1 e2
                    | Times(el)::[] ->
                      let p = Times(el) in
                      let s = simplify1 p in
                      let e2 = Times(hd::s::[]) in
                        simplify1 e2
                )
              | _ ->
                let hd = simplify1 hd in
                let e2 = Times(hd::tl) in
                  simplify1 e2
            )
          | _ -> e
        )
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
    let rE = simplify1(e) in
      print_pExp rE;
      if (equal_pExp e rE) then
        e
      else  
        simplify(rE)
;;



