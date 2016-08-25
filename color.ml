open Graph
open Instruction
open Expr
open Printf

let rec find ls x =
  match ls with
    | [] -> None
    | (y,v)::rest ->
      if y = x then Some(v) else find rest x

let findknown ls x =
  match find ls x with
    | None -> failwith "Not found in findknown"
    | Some(v) -> v

(* This example was helpful in generating the graph code: http://ocamlgraph.lri.fr/sudoku.ml *)

(* A module for constructing graphs whose vertices are strings *)
module G = Imperative.Graph.Abstract(struct type t = string end)

(* A module for coloring G-graphs *)
module C = Coloring.Mark(G)

let color_graph (colors : int) (nodes : string list) (edges : (string * string) list) : ((string * int) list) option =
  let g = G.create () in
  let add_vertex s =
    let vertex = G.V.create s in
    G.add_vertex g vertex;
    (s, vertex) in
  let vertices = List.map add_vertex nodes in
  let add_edge (source, dest) =
   
    
    let v1, v2 = (findknown vertices source, findknown vertices dest) in
    G.add_edge g v1 v2 in
  List.iter add_edge edges;
  begin try
    C.coloring g colors;
    Some(List.map (fun v -> (v, G.Mark.get (findknown vertices v))) nodes)
  with
    | _ -> None
  end

(* Return all the identifiers that are defined in this expression (e.g. appear
in let bindings) to use for building an environment *)

let rec parse_cexpr (ce : cexpr) : string list = 
  match ce with 
    | CPrim1(_, ImmId(id)) -> [id]
    | CPrim2(_, ImmId(id1), ImmId(id2)) -> [id1;id2]
    | CPrim2(_, ImmId(id), _) -> [id]
    | CPrim2(_, _, ImmId(id)) -> [id]
    | CApp(_,vars) -> (List.map (fun x-> match x with
                                            |ImmId(id)-> id) vars)
    | CIf(ImmBool(b), tbranch, fbranch) -> 
        let a = (getvars tbranch) in
        let b = (getvars fbranch) in
        (a@b)
    | CIf(ImmId(s), tbranch, fbranch) -> 
        let a = (getvars tbranch) in
        let b = (getvars fbranch) in
        (a@b)
    | CIf(ImmNumber(n), tbranch, fbranch) -> 
        let a = (getvars tbranch) in
        let b = (getvars fbranch) in
        (a@b)
    | CImmExpr(ImmId(id)) -> [id]
    | _ -> []

and getvars (ae : aexpr) : string list =
  match ae with 
    | ALet(var, cex, aex) -> var::(parse_cexpr cex) @ (getvars aex)
    | ACExpr(cex) -> (parse_cexpr cex)

let rec find ls x =
  match ls with
    | [] -> None
    | y::rest ->
      if y = x then Some(true) else find rest x

let rec remove_funvars xs vars = 
    match xs with
      | (x,y)::rest -> 
        begin match ((find vars x), (find vars y)) with
            | (Some(v1), Some(v2)) -> (x,y)::(remove_funvars rest vars)
            | (_) -> (remove_funvars rest vars) end
      | [] -> []

let rec color_assign (var_color : ((string * int) list)) (registers : reg list): (location envt) =
 
   
    match var_color with
     
      | ((var, color)::rest) ->  if color <= (List.length registers) then (var, LReg(List.nth registers (color-1)))::(color_assign rest registers) else (var, LStack(color))::(color_assign rest registers)
      | [] -> []
  
let get_colors (registers : reg list) (varlist : string list) (edgelist : (string * string) list) : (location envt) =
  let fixed_edges = (remove_funvars edgelist varlist) in 
  let color = match (color_graph (List.length varlist) varlist fixed_edges) with 
  
                | None -> []
                | Some(x) -> x
              in 
  (color_assign color registers)

let rec remove x xs =
  match xs with
    | y::xs -> if x = y then remove x xs else y::(remove x xs)
    | [] -> []

let rec remove_duplicates xs =
  match xs with
    | x::xs -> x::(remove_duplicates (remove x xs))
    | [] -> []

let rec dep_graph_ae (ae : aexpr) (actives : string list) : (string list * (string * string) list) = 
  match ae with 
    | ALet(id, ce, body) ->
        let (update, edges) = (dep_graph_ae body actives) in
        let okay= (remove id update) in
        let (update2, edges2) = (dep_graph_ce ce okay) in 
        let rem_id = (remove id update2) in 
        let new_edges = (List.map (fun x-> (id, x)) rem_id) in 
        (rem_id, (new_edges@edges@edges2))
    | ACExpr(ce) -> (dep_graph_ce ce actives)

and dep_graph_ce (ce : cexpr) (actives : string list) :  (string list * (string * string) list)= 
  match ce with
    | CIf(cond, thn, els) -> 
        let cond_id = (parse_cexpr (CImmExpr(cond))) in
        let (thn_active, thn_edges) = (dep_graph_ae thn actives) in 
        let (els_active, els_edges)  = (dep_graph_ae els actives) in
        let okay= thn_active@els_active@cond_id in
        let merge=remove_duplicates okay in
        (merge, thn_edges@els_edges)
    | _ -> 
        let vars = (parse_cexpr ce) in
        let rem_dup = (remove_duplicates (actives@vars)) in 
        (rem_dup, [])
 
let dep_graph (ae : aexpr) : (string * string) list =
  match (dep_graph_ae ae []) with
    | (actives, edges) -> edges

let colorful_env (ae : aexpr) : location envt =
  let deps = dep_graph ae in
  (* spare_regs is a list that contains the usable registers for your
  implementation; it is set by the NUMREGS option as well *)
 
  get_colors !spare_regs (getvars ae) deps

