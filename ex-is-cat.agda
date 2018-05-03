
-- Main file
--
-- authors: Simon Forest and Samuel Mimram

open import Agda.Builtin.Equality
open import 3cat
open import ex
open import Relation.Nullary

open import units
open import assoc10
open import assoc20
open import assoc21
open import assoc30
open import assoc31
open import assoc32
open import comp10-id
open import comp20-id
open import comp21-id
open import ich210
open import ich310
open import ich320
open import ich321


-- Proof that the 3PCat C is in fact a 3-category

D : 3Cat C

3Cat.unit10-l D = unit10-l
3Cat.unit10-r D = unit10-r
3Cat.unit20-l D = unit20-l
3Cat.unit20-r D = unit20-r
3Cat.unit21-l D = unit21-l
3Cat.unit21-r D = unit21-r
3Cat.unit30-l D = unit30-l
3Cat.unit30-r D = unit30-r
3Cat.unit31-l D = unit31-l
3Cat.unit31-r D = unit31-r
3Cat.unit32-l D = unit32-l
3Cat.unit32-r D = unit32-r
3Cat.assoc10 D = assoc10
3Cat.assoc20 D = assoc20
3Cat.assoc21 D = assoc21
3Cat.assoc30 D = assoc30
3Cat.assoc31 D = assoc31
3Cat.assoc32 D = assoc32
3Cat.comp10-id D = comp10-id
3Cat.comp20-id D = comp20-id
3Cat.comp21-id D = comp21-id
3Cat.ich210 D = ich210
3Cat.ich310 D = ich310
3Cat.ich320 D = ich320
3Cat.ich321 D = ich321

cella = (C1-xy C1-a)
cellb = (C1-xy C1-b)
cellc = (C1-xy C1-c)
celld = (C1-yz C1-d)
celle = (C1-yz C1-e)
cellf = (C1-yz C1-f)

cellA = C2-xy (C2-AB-A C2-A)
cellA' = C2-xy (C2-AB-A C2-A')
cellB = C2-xy (C2-AB-B C2-B)
cellB' = C2-xy (C2-AB-B C2-B')
cellC = C2-yz (C2-CD-C C2-C)
cellC' = C2-yz (C2-CD-C C2-C')
cellD = C2-yz (C2-CD-D C2-D)
cellD' = C2-yz (C2-CD-D C2-D')

cellΓ = C3-Γ
cellΘ = C3-Θ

s : C2 (3PCat.comp10 C cella celld) (3PCat.comp10 C cellc cellf)
s = 3PCat.comp20 C (3PCat.comp21 C cellA cellB) (3PCat.comp21 C cellC cellD)

t : C2 (3PCat.comp10 C cella celld) (3PCat.comp10 C cellc cellf)
t = 3PCat.comp20 C (3PCat.comp21 C cellA' cellB') (3PCat.comp21 C cellC' cellD')

-- Proof that the two compositions "Θ then Γ" "Θ then Γ" are different

cellΘΓ : C3 s t
cellΘΓ =
  let c1 = 3PCat.comp30 C (3PCat.id2 C cellA) (3PCat.id2 C (3PCat.id1 C celld)) in
  let c2 = 3PCat.comp30 C (3PCat.id2 C (3PCat.id1 C cellc)) (3PCat.id2 C cellD) in
  let first = 3PCat.comp31 C (3PCat.comp31 C c1 cellΘ) c2 in
  let c3 = 3PCat.comp30 C (3PCat.id2 C (3PCat.id1 C cella)) (3PCat.id2 C cellC') in
  let c4 = 3PCat.comp30 C (3PCat.id2 C cellB') (3PCat.id2 C (3PCat.id1 C cellf)) in
  let second = 3PCat.comp31 C (3PCat.comp31 C c3 cellΓ) c4 in
  3PCat.comp32 C first second

cellΓΘ : C3 s t
cellΓΘ =
  let c1 = 3PCat.comp30 C (3PCat.id2 C (3PCat.id1 C cella)) (3PCat.id2 C cellC) in
  let c2 = 3PCat.comp30 C (3PCat.id2 C cellB) (3PCat.id2 C (3PCat.id1 C cellf)) in
  let first = 3PCat.comp31 C (3PCat.comp31 C c1 cellΓ) c2 in
  let c3 = 3PCat.comp30 C (3PCat.id2 C cellA') (3PCat.id2 C (3PCat.id1 C celld)) in
  let c4 = 3PCat.comp30 C (3PCat.id2 C (3PCat.id1 C cellc)) (3PCat.id2 C cellD') in
  let second = 3PCat.comp31 C (3PCat.comp31 C c3 cellΘ) c4 in
  3PCat.comp32 C first second

main-lemma : ¬ cellΘΓ ≡ cellΓΘ
main-lemma () 
