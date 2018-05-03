module List = struct
  include List

  let map_pairs f l1 l2 =
    List.flatten (List.map (fun x -> List.map (f x) l2) l1)
end

(* type var = ref int *)
(* let var = *)
  (* let n = ref (-1) in *)
  (* fun () -> incr n; (!n : var) *)

type c0 = C0_x | C0_y | C0_z

type c1_abc = C1_a | C1_b | C1_c

type c1_def = C1_d | C1_e | C1_f

type c1 =
  | C1_id of c0
  | C1_xy of c1_abc
  | C1_yz of c1_def
  | C1_xz of c1_abc * c1_def

type c2_aa = C2_a | C2_a'

type c2_bb = C2_b | C2_b'

type c2_cc = C2_c | C2_c'

type c2_dd = C2_d | C2_d'

type c2_ab =
  | C2_ab_id of c1_abc
  | C2_ab_a  of c2_aa
  | C2_ab_b  of c2_bb
  | C2_ab_ab of c2_aa * c2_bb

type c2_cd =
  | C2_cd_id of c1_def
  | C2_cd_c  of c2_cc
  | C2_cd_d  of c2_dd
  | C2_cd_cd of c2_cc * c2_dd

type c2 =
  | C2_xx of c0
  | C2_xy of c2_ab
  | C2_yz of c2_cd
  | C2_xz of c2_ab * c2_cd

type c3 =
  | C3_id of c2
  | C3_G of c2_bb option * c2_cc option
  | C3_T of c2_aa option * c2_dd option
  | C3_GT
  | C3_TG

let src10_abc (_:c1_abc) = C0_x

let src10_def (_:c1_def) = C0_y

let src10 = function
  | C1_id x -> x
  | C1_xy a -> src10_abc a
  | C1_yz d -> src10_def d
  | C1_xz (a,d) -> src10_abc a

let tgt10_abc (_:c1_abc) = C0_y

let tgt10_def (_:c1_def) = C0_z

let tgt10 = function
  | C1_id x -> x
  | C1_xy a -> tgt10_abc a
  | C1_yz d -> tgt10_def d
  | C1_xz (a,d) -> tgt10_def d

let src21_ab = function
  | C2_ab_id a -> a
  | C2_ab_a  _ -> C1_a
  | C2_ab_b  _ -> C1_b
  | C2_ab_ab _ -> C1_a

let src21_cd = function
  | C2_cd_id a -> a
  | C2_cd_c  _ -> C1_d
  | C2_cd_d  _ -> C1_e
  | C2_cd_cd _ -> C1_d

let src21 = function
  | C2_xx x -> C1_id x
  | C2_xy a -> C1_xy (src21_ab a)
  | C2_yz c -> C1_yz (src21_cd c)
  | C2_xz (a,c) -> C1_xz (src21_ab a, src21_cd c)

let src32 = function
  | C3_id f -> f
  | C3_G (None, None) -> C2_xz (C2_ab_a C2_a, C2_cd_d C2_d)
  | C3_G (Some b, None) -> C2_xz (C2_ab_ab (C2_a,b), C2_cd_d C2_d)
  | C3_G (None, Some c) -> C2_xz (C2_ab_a C2_a, C2_cd_cd (c, C2_d))
  | C3_G (Some b, Some c) -> C2_xz (C2_ab_ab (C2_a, b), C2_cd_cd (c, C2_d))
  | C3_T (None, None) -> C2_xz (C2_ab_b C2_b, C2_cd_c C2_c)
  | C3_T (Some a, None) -> C2_xz (C2_ab_ab (a,C2_b), C2_cd_c C2_c)
  | C3_T (None, Some d) -> C2_xz (C2_ab_b C2_b, C2_cd_cd (C2_c,d))
  | C3_T (Some a, Some d) -> C2_xz (C2_ab_ab(a,C2_b), C2_cd_cd(C2_c,d))
  | C3_GT -> C2_xz (C2_ab_ab (C2_a, C2_b), C2_cd_cd (C2_c, C2_d))
  | C3_TG -> C2_xz (C2_ab_ab (C2_a, C2_b), C2_cd_cd (C2_c, C2_d))

let tgt32 = function
  | C3_id f -> f
  | C3_G (None, None) -> C2_xz (C2_ab_a C2_a', C2_cd_d C2_d')
  | C3_G (Some b, None) -> C2_xz (C2_ab_ab (C2_a',b), C2_cd_d C2_d')
  | C3_G (None, Some c) -> C2_xz (C2_ab_a C2_a', C2_cd_cd (c, C2_d'))
  | C3_G (Some b, Some c) -> C2_xz (C2_ab_ab (C2_a', b), C2_cd_cd (c, C2_d'))
  | C3_T (None, None) -> C2_xz (C2_ab_b C2_b', C2_cd_c C2_c')
  | C3_T (Some a, None) -> C2_xz (C2_ab_ab (a,C2_b'), C2_cd_c C2_c')
  | C3_T (None, Some d) -> C2_xz (C2_ab_b C2_b', C2_cd_cd (C2_c',d))
  | C3_T (Some a, Some d) -> C2_xz (C2_ab_ab(a,C2_b'), C2_cd_cd(C2_c',d))
  | C3_GT -> C2_xz (C2_ab_ab (C2_a', C2_b'), C2_cd_cd (C2_c', C2_d'))
  | C3_TG -> C2_xz (C2_ab_ab (C2_a', C2_b'), C2_cd_cd (C2_c', C2_d'))

let tgt21_ab = function
  | C2_ab_id a -> a
  | C2_ab_a  _ -> C1_b
  | C2_ab_b  _ -> C1_c
  | C2_ab_ab _ -> C1_c

let tgt21_cd = function
  | C2_cd_id a -> a
  | C2_cd_c  _ -> C1_e
  | C2_cd_d  _ -> C1_f
  | C2_cd_cd _ -> C1_f

let tgt21 = function
  | C2_xx x -> C1_id x
  | C2_xy a -> C1_xy (tgt21_ab a)
  | C2_yz c -> C1_yz (tgt21_cd c)
  | C2_xz (a,c) -> C1_xz (tgt21_ab a, tgt21_cd c)

let src20 f = src10 (src21 f)
let tgt20 f = src10 (src21 f)
let src31 f = src21 (src32 f)
let tgt31 f = tgt21 (tgt32 f)
let src30 f = src10 (src31 f)
let tgt30 f = tgt10 (tgt31 f)

(*** Printing ***)

let string0 = function
  | C0_x -> "C0-x"
  | C0_y -> "C0-y"
  | C0_z -> "C0-z"

let string1_abc = function
  | C1_a -> "C1-a"
  | C1_b -> "C1-b"
  | C1_c -> "C1-c"

let string1_def = function
  | C1_d -> "C1-d"
  | C1_e -> "C1-e"
  | C1_f -> "C1-f"

let string1 = function
  | C1_id x -> "(C1-id " ^ string0 x ^ ")"
  | C1_xy a -> "(C1-xy " ^ string1_abc a ^ ")"
  | C1_yz d -> "(C1-yz " ^ string1_def d ^ ")"
  | C1_xz (a,d) -> "(C1-xz " ^ string1_abc a ^ " " ^ string1_def d ^ ")"

let string2_aa = function
  | C2_a -> "C2-A"
  | C2_a' -> "C2-A'"

let string2_bb = function
  | C2_b -> "C2-B"
  | C2_b' -> "C2-B'"

let string2_cc = function
  | C2_c -> "C2-C"
  | C2_c' -> "C2-C'"

let string2_dd = function
  | C2_d -> "C2-D"
  | C2_d' -> "C2-D'"

let string2_ab = function
  | C2_ab_id a -> "(C2-AB-id " ^ string1_abc a ^ ")"
  | C2_ab_a a -> "(C2-AB-A " ^ string2_aa a ^ ")"
  | C2_ab_b b -> "(C2-AB-B " ^ string2_bb b ^ ")"
  | C2_ab_ab(a,b) -> "(C2-AB-AB " ^ string2_aa a ^ " " ^ string2_bb b ^ ")"

let string2_cd = function
  | C2_cd_id d -> "(C2-CD-id " ^ string1_def d ^ ")"
  | C2_cd_c c -> "(C2-CD-C " ^ string2_cc c ^ ")"
  | C2_cd_d d -> "(C2-CD-D " ^ string2_dd d ^ ")"
  | C2_cd_cd(c,d) -> "(C2-CD-CD " ^ string2_cc c ^ " " ^ string2_dd d ^ ")"

let string2 = function
  | C2_xx x -> "(C2-xx " ^ string0 x ^ ")"
  | C2_xy a -> "(C2-xy " ^ string2_ab a ^ ")"
  | C2_yz c -> "(C2-yz " ^ string2_cd c ^ ")"
  | C2_xz (a,c) -> "(C2-xz " ^ string2_ab a ^ " " ^ string2_cd c ^ ")"

let string3 = function
  | C3_id f -> "(C3-id " ^ string2 f ^ ")"
  | C3_G (None, None) -> "C3-Γ"
  | C3_G (Some b, None) -> "(C3-Γ-B " ^ string2_bb b ^ ")"
  | C3_G (None, Some c) -> "(C3-Γ-C " ^ string2_cc c ^ ")"
  | C3_G (Some b, Some c) -> "(C3-Γ-BC " ^ string2_bb b ^ " " ^ string2_cc c ^ ")"
  | C3_T (None, None) -> "C3-Θ"
  | C3_T (Some a, None) -> "(C3-Θ-A " ^ string2_aa a ^ ")"
  | C3_T (None, Some d) -> "(C3-Θ-D " ^ string2_dd d ^ ")"
  | C3_T (Some a, Some d) -> "(C3-Θ-AD " ^ string2_aa a ^ " " ^ string2_dd d ^ ")"
  | C3_GT -> "C3-ΓΘ"
  | C3_TG -> "C3-ΘΓ"

(*** Enumeration ***)

let c0 = [C0_x; C0_y; C0_z]
let c1_abc = [C1_a; C1_b; C1_c]
let c1_def = [C1_d; C1_e; C1_f]
let c1 =
  (List.map (fun x -> C1_id x) c0)
  @(List.map (fun a -> C1_xy a) c1_abc)
  @(List.map (fun b -> C1_yz b) c1_def)
  @(List.map_pairs (fun a b -> C1_xz(a,b)) c1_abc c1_def)
let c2_aa = [C2_a; C2_a']
let c2_bb = [C2_b; C2_b']
let c2_cc = [C2_c; C2_c']
let c2_dd = [C2_d; C2_d']
let c2_ab =
  (List.map (fun a -> C2_ab_id a) c1_abc)
  @(List.map (fun a -> C2_ab_a a) c2_aa)
  @(List.map (fun b -> C2_ab_b b) c2_bb)
  @(List.map_pairs (fun a b -> C2_ab_ab (a,b)) c2_aa c2_bb)
let c2_cd =
  (List.map (fun d -> C2_cd_id d) c1_def)
  @(List.map (fun c -> C2_cd_c c) c2_cc)
  @(List.map (fun d -> C2_cd_d d) c2_dd)
  @(List.map_pairs (fun c d -> C2_cd_cd (c,d)) c2_cc c2_dd)
let c2 =
  (List.map (fun x -> C2_xx x) c0)
  @(List.map (fun a -> C2_xy a) c2_ab)
  @(List.map (fun c -> C2_yz c) c2_cd)
  @(List.map_pairs (fun a c -> C2_xz(a,c)) c2_ab c2_cd)
let c3 =
  (List.map (fun f -> C3_id f) c2)
  @[C3_G (None,None)]
  @(List.map (fun b -> C3_G (Some b, None)) c2_bb)
  @(List.map (fun c -> C3_G (None, Some c)) c2_cc)
  @(List.map_pairs (fun b c -> C3_G (Some b, Some c)) c2_bb c2_cc)
  @[C3_T (None,None)]
  @(List.map (fun a -> C3_T (Some a, None)) c2_aa)
  @(List.map (fun d -> C3_T (None, Some d)) c2_dd)
  @(List.map_pairs (fun a d -> C3_T (Some a, Some d)) c2_aa c2_dd)
  @[C3_GT; C3_TG]

let () =
  if Array.length Sys.argv <= 1 then exit 0;
  match Sys.argv.(1) with
  | "assoc21" ->
     let l = List.map_pairs (fun f g -> (f,g)) c2 c2 in
     let l = List.filter (fun (f,g) -> tgt21 f = src21 g) l in
     let l = List.map_pairs (fun (f,g) h -> (f,g,h)) l c2 in
     let l = List.filter (fun (f,g,h) -> tgt21 g = src21 h) l in
     List.iter (fun (f,g,h) -> Printf.printf "3Cat.assoc21 C %s %s %s = refl\n%!" (string2 f) (string2 g) (string2 h)) l
  | "assoc30" ->
     let l = List.map_pairs (fun f g -> (f,g)) c3 c3 in
     let l = List.filter (fun (f,g) -> tgt30 f = src30 g) l in
     let l = List.map_pairs (fun (f,g) h -> (f,g,h)) l c3 in
     let l = List.filter (fun (f,g,h) -> tgt30 g = src30 h) l in
     List.iter (fun (f,g,h) -> Printf.printf "3Cat.assoc30 C %s %s %s = refl\n%!" (string3 f) (string3 g) (string3 h)) l
  | "assoc31" ->
     let l = List.map_pairs (fun f g -> (f,g)) c3 c3 in
     let l = List.filter (fun (f,g) -> tgt31 f = src31 g) l in
     let l = List.map_pairs (fun (f,g) h -> (f,g,h)) l c3 in
     let l = List.filter (fun (f,g,h) -> tgt31 g = src31 h) l in
     List.iter (fun (f,g,h) -> Printf.printf "3Cat.assoc31 C %s %s %s = refl\n%!" (string3 f) (string3 g) (string3 h)) l
  | "ich210" ->
     let l = List.map_pairs (fun f g -> (f,g)) c2 c2 in
     let l = List.filter (fun (f,g) -> tgt21 f = src21 g) l in
     let l = List.map_pairs (fun (f,f') (g,g') -> f,f',g,g') l l in
     let l = List.filter (fun (f,f',g,g') -> tgt20 f = src20 g) l in
     List.iter (fun (f,f',g,g') -> Printf.printf "3Cat.ich210 C %s %s %s %s = refl\n%!" (string2 f) (string2 f') (string2 g) (string2 g')) l
  | "ich310" ->
     let l = List.map_pairs (fun f g -> (f,g)) c3 c3 in
     let l = List.filter (fun (f,g) -> tgt31 f = src31 g) l in
     let l = List.map_pairs (fun (f,f') (g,g') -> f,f',g,g') l l in
     let l = List.filter (fun (f,f',g,g') -> tgt30 f = src30 g) l in
     List.iter (fun (f,f',g,g') -> Printf.printf "3Cat.ich310 C %s %s %s %s = refl\n%!" (string3 f) (string3 f') (string3 g) (string3 g')) l
  | "ich320" ->
     let l = List.map_pairs (fun f g -> (f,g)) c3 c3 in
     let l = List.filter (fun (f,g) -> tgt32 f = src32 g) l in
     let l = List.map_pairs (fun (f,f') (g,g') -> f,f',g,g') l l in
     let l = List.filter (fun (f,f',g,g') -> tgt30 f = src30 g) l in
     List.iter (fun (f,f',g,g') -> Printf.printf "3Cat.ich320 C %s %s %s %s = refl\n%!" (string3 f) (string3 f') (string3 g) (string3 g')) l
  | "ich321" ->
     let l = List.map_pairs (fun f g -> (f,g)) c3 c3 in
     let l = List.filter (fun (f,g) -> tgt32 f = src32 g) l in
     let l = List.map_pairs (fun (f,f') (g,g') -> f,f',g,g') l l in
     let l = List.filter (fun (f,f',g,g') -> tgt31 f = src31 g) l in
     List.iter (fun (f,f',g,g') -> Printf.printf "3Cat.ich321 C %s %s %s %s = refl\n%!" (string3 f) (string3 f') (string3 g) (string3 g')) l
  | _ -> ()
