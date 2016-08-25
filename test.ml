open Compile
open Instruction
open Expr
open Runner
open Printf
open OUnit2
open ExtLib
open Color

let rec take l n =
  if n == 0 then []
  else
    match l with
      | [] -> failwith "took too many"
      | x::xs -> x::(take xs (n - 1))


let t name program expected = name>::test_run program name expected;;
let tvg name program expected = name>::test_run_valgrind program name expected;;
let terr name program expected = name>::test_err program name expected;;
let tdep name program expected = name>::fun ctxt ->
  let p = parse_string name program in
  let a = anf_program p in
  let answer = match a with
    | AProgram(decls, body) ->
      let deps = (dep_graph body) in
      deps in
  let c = Pervasives.compare in
  assert_equal (List.sort ~cmp:c expected) (List.sort ~cmp:c answer) ~printer:dump;;

let tcolor name program expected_colors = name>::fun ctxt ->
  let p = parse_string name program in
  let a = anf_program p in
  let body = match a with
    | AProgram(decls, body) -> body in
  let vars = getvars body in
  let edges = (dep_graph body) in
  let coloring = get_colors [] vars edges in
  let stackmax = List.fold_right (fun (_, l) m ->
    match l with
      | LStack(n) -> if n > m then n else m
      | LReg _ -> m) coloring 0 in
  assert_equal expected_colors stackmax ~printer:dump;;

let deps = [
 (* tdep "d0" "let x = 5 in x"
    [];*)
   tdep "yooo2" 
  "
  let k=5 in
  let t=k>6 in
  if t: 3 else: false"
  [("t","k")];
  
    tdep "okay" 
   "let a = 10 + 10 in 
    let t= a<20 in
    let b = (if t: 
            let c = 5 in 
            let d = 5 + c in 
            d
            else:
              let k=4 in 
              let z=k+2 in
              z) in b+1
    "
    [("b", "t"); ("d", "c"); ("t", "a"); ("z", "k")];

  tdep "writeup1"
    "
let n = 5 * 5 in
let m = 6 * 6 in
let x = n + 1 in
let y = m + 1 in
x + y
    "
    [("m", "n"); ("x", "m"); ("x", "n"); ("y", "m"); ("y", "x")];

     tdep "writeup2"
    "let b=4 in
     let x=10 in
     let i= if true: 
       let z=11 in 
        z+b
        else:
         let y=7 in
        y+1 in
     let a =5+i in
     a+x
    "
    [("a","i"); ("a","x"); ("i","b"); ("i", "x"); ("x", "b"); ("y","x"); ("z", "b"); ("z", "x")];

    tdep "dep1" 
    " 
let a = 1 in
let b = a + 1 in 
let c = a + b + 1 in
let d = a + b + c + 1 in
let e = a + b + c + d + 1 in
let f = a + b + c + d + e + 1 in 
let g = a + b + c + d + e + f + 1 in 
a + b + c + d + e + f + g 
    " 
    [("b", "a"); ("c", "a"); ("c", "b"); ("c", "temp__1"); ("d", "a"); ("d", "b"); ("d", "c"); ("d", "temp__3"); ("e", "a"); ("e", "b"); ("e", "c"); ("e", "d"); ("e", "temp__6"); ("f", "a"); ("f", "b"); ("f", "c"); ("f", "d"); ("f", "e"); ("f", "temp__10"); ("g", "a"); ("g", "b"); ("g", "c"); ("g", "d"); ("g", "e"); ("g", "f"); ("g", "temp__15"); ("temp__1", "a"); ("temp__1", "b"); ("temp__10", "a"); ("temp__10", "b"); ("temp__10", "c"); ("temp__10", "d"); ("temp__10", "e"); ("temp__10", "temp__9"); ("temp__11", "a"); ("temp__11", "b"); ("temp__11", "c"); ("temp__11", "d"); ("temp__11", "e"); ("temp__11", "f"); ("temp__12", "a"); ("temp__12", "b"); ("temp__12", "c"); ("temp__12", "d"); ("temp__12", "e"); ("temp__12", "f"); ("temp__12", "temp__11"); ("temp__13", "a"); ("temp__13", "b"); ("temp__13", "c"); ("temp__13", "d"); ("temp__13", "e"); ("temp__13", "f"); ("temp__13", "temp__12"); ("temp__14", "a"); ("temp__14", "b"); ("temp__14", "c"); ("temp__14", "d"); ("temp__14", "e"); ("temp__14", "f"); ("temp__14", "temp__13"); ("temp__15", "a"); ("temp__15", "b"); ("temp__15", "c"); ("temp__15", "d"); ("temp__15", "e"); ("temp__15", "f"); ("temp__15", "temp__14"); ("temp__16", "a"); ("temp__16", "b"); ("temp__16", "c"); ("temp__16", "d"); ("temp__16", "e"); ("temp__16", "f"); ("temp__16", "g"); ("temp__17", "c"); ("temp__17", "d"); ("temp__17", "e"); ("temp__17", "f"); ("temp__17", "g"); ("temp__17", "temp__16"); ("temp__18", "d"); ("temp__18", "e"); ("temp__18", "f"); ("temp__18", "g"); ("temp__18", "temp__17"); ("temp__19", "e"); ("temp__19", "f"); ("temp__19", "g"); ("temp__19", "temp__18"); ("temp__2", "a"); ("temp__2", "b"); ("temp__2", "c"); ("temp__20", "f"); ("temp__20", "g"); ("temp__20", "temp__19"); ("temp__3", "a"); ("temp__3", "b"); ("temp__3", "c"); ("temp__3", "temp__2"); ("temp__4", "a"); ("temp__4", "b"); ("temp__4", "c"); ("temp__4", "d"); ("temp__5", "a"); ("temp__5", "b"); ("temp__5", "c"); ("temp__5", "d"); ("temp__5", "temp__4"); ("temp__6", "a"); ("temp__6", "b"); ("temp__6", "c"); ("temp__6", "d"); ("temp__6", "temp__5"); ("temp__7", "a"); ("temp__7", "b"); ("temp__7", "c"); ("temp__7", "d"); ("temp__7", "e"); ("temp__8", "a"); ("temp__8", "b"); ("temp__8", "c"); ("temp__8", "d"); ("temp__8", "e"); ("temp__8", "temp__7"); ("temp__9", "a"); ("temp__9", "b"); ("temp__9", "c"); ("temp__9", "d"); ("temp__9", "e"); ("temp__9", "temp__8")]; 

 tdep "dep2" "
   def f(a,b,c):
    let t=a>5 in
    if t: b else: c
 let x = 11 in
let y = 21 in
let z = 31 in 
f(x,y,z)
    "
     [("y", "x"); ("z", "x"); ("z", "y")]
    ; 
 
] 

let colors = [
  tcolor "okay1" 
   "let a = 10 + 10 in 
    let t= a<20 in
    let b = (if t: 
            let c = 5 in 
            let d = 5 + c in 
            d
            else:
              let k=4 in 
              let z=k+2 in
              z) in b+1
    "
    2;

  tcolor "yooo2" 
  "
  let k=5 in
  let t=k>6 in
  if t: 3 else: false"
  2;

  tcolor "writeup2c"
    "
let n = 5 * 5 in
let m = 6 * 6 in
let x = n + 1 in
let y = m + 1 in
let z = x + y in
let k = z * z in
let g = k + 5 in
k + 3
    "
    3;

     tcolor "writeup2k"
    "
        let n = 5 * 5 in
        let m = 6 * 6 in
        let l= 2*2 in
        let z=l+1 in
        let t=z+1 in 
        let x = n + 1 in
        let y = m + 1 in
        let z = x + y in
        let k = z * z in
        let g = k + 5 in
        k + 3
        "
        5; 

    tcolor "color_test1" 
    " 
let a = 1 in
let b = a + 1 in 
let c = a + b + 1 in
let d = a + b + c + 1 in
let e = a + b + c + d + 1 in
let f = a + b + c + d + e + 1 in 
let g = a + b + c + d + e + f + 1 in 
let h = a + b + c + d + e + f + g + 1 in
let i = a + b + c + d + e + f + g + h + 1 in
let j = a + b + c + d + e + f + g + h + i + 1 in 
let k = a + b + c + d + e + f + g + h + i + j + 1 in 
a + b + c + d + e + f + g + h + i + j + k 
    " 
    13; 

    tcolor "color_test2" 
    " 
let a = 1 in
let b = a + 1 in 
let c = a + b + 1 in
let d = a + b + c + 1 in
let e = a + b + c + d + 1 in
let f = a + b + c + d + e + 1 in 
let g = a + b + c + d + e + f + 1 in 
a + b + c + d + e + f + g 
    " 
    9; 

    tcolor "color_test3" 
    " 
let a = 10 + 10 in 
let b = (if true: 
            let c = 5 in 
            let d = 5 + c in 
            let e = 5 + c + d in
            let f = (if false:
                        let g = e + 5 in 
                        g 
                    else: 
                        let g = e + 10 in 
                        let h = g + 1 in 
                        h) in 
            f
        else:
            let c = 10 in
            let d = 10 + c in
            let e = 10 + c + d in 
            e) in
        a + b
    "
    4; 

    tcolor "color_test4"
    "
    let b=4 in
     let x=10 in
     let i= if true: 
       let z=11 in 
        z+b
        else:
         let y=7 in
        y+1 in
     let a =5+i in
     a+x
    "

    4;
]
let test= [
    t "test_1" 
   "let a = 10 + 10 in 
    let t= a<20 in
    let b = (if t: 
            let c = 5 in 
            let d = 5 + c in 
            d
            else:
              let k=4 in 
              let z=k+2 in
              z) in b+1
    "
    "7";
    t "yooo3" 
  "
  let k=5 in
  let t=k>6 in
  if t: 3 else: false"
  "false";
   t "okay" 
   "let a = 10 + 10 in 
    let t= a<20 in
    let b = (if t: 
            let c = 5 in 
            let d = 5 + c in 
            d
            else:
              let k=4 in 
              let z=k+2 in
              z) in b+1
    "
    "7";


    t "test1"
    "
    let n = 5 * 5 in
    let m = 6 * 6 in
    let x = n + 1 in
    let y = m + 1 in
    let z = x + y in
    let k = z * z in
    let g = k + 5 in
    k + 3
    "
    "3972";

    t "test2" 
    " 
let a = 1 in
let b = a + 1 in                
let c = a + b + 1 in   
let
 d = a + b + c + 1 in
let e = a + b + c + d + 1 in
let f = a + b + c + d + e + 1 in 
let g = a + b + c + d + e + f + 1 in 
let h = a + b + c + d + e + f + g + 1 in
let i = a + b + c + d + e + f + g + h + 1 in
let j = a + b + c + d + e + f + g + h + i + 1 in 
let k = a + b + c + d + e + f + g + h + i + j + 1 in 
a + b + c + d + e + f + g + h + i + j + k 
    " 
    "2047"; 

    t "test3" 
    " 
let a = 1 in
let b = a + 1 in 
let c = a + b + 1 in
let d = a + b + c + 1 in
let e = a + b + c + d + 1 in
let f = a + b + c + d + e + 1 in 
let g = a + b + c + d + e + f + 1 in 
a + b + c + d + e + f + g 
    " 
    "127";
    
    t "test4"     
    " 
let a = 10 + 10 in 
let t= a<20 in let b = (if t: 
            let c = 5 in 
            let d = 5 + c in 
            let e = 5 + c + d in
            let f = (if false:
                        let g = e + 5 in 
                        g 
                    else: 
                        let g = e + 10 in 
                        let h = g + 1 in 
                        h) in 
            f
        else:
            let c = 10 in
            let d = 10 + c in
            let e = 10 + c + d in 
            e) in
        a + b
    "
    "60"; 

    t "test5" 
    "
def f(a,b,c):
    let t=a>5 in
    if t: b else: c
let x = 11 in
let y = 21 in
let z = 31 in 
f(x,y,z)
    "
    "21"; 
 
] 
let suite =
"suite">::: deps@colors@test

let () =
  run_test_tt_main suite
;;

