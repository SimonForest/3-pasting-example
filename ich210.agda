
-- (2,1,0)-exchange proof
--
-- authors: Simon Forest and Samuel Mimram

open import Agda.Builtin.Equality
open import Relation.Binary.PropositionalEquality
open import 3cat
open import assoc21
open import ex

distrib210l : {x y z : C0}  {g1 g2 g3 : C1 y z} (f : C1 x y) (v1 : C2 g1 g2) (v2 : C2 g2 g3) → 3PCat.comp20 C (3PCat.id1 C f) (3PCat.comp21 C v1 v2) ≡ 3PCat.comp21 C (3PCat.comp20 C (3PCat.id1 C f) v1) (3PCat.comp20 C (3PCat.id1 C f) v2)
distrib210l (C1-id x) (C2-xx .x) (C2-xx .x) = refl
distrib210l (C1-id .C0-x) (C2-xy A) (C2-xy A₁) = refl
distrib210l (C1-id .C0-y) (C2-yz A) (C2-yz A₁) = refl
distrib210l (C1-id .C0-x) (C2-xz A C₁) (C2-xz A₁ C₂) = refl
distrib210l (C1-xy x) (C2-xx .C0-y) (C2-xx .C0-y) = refl
distrib210l (C1-xy C1-a) (C2-yz (C2-CD-id a)) (C2-yz (C2-CD-id .a)) = refl
distrib210l (C1-xy C1-a) (C2-yz (C2-CD-id .C1-d)) (C2-yz (C2-CD-C x)) = refl
distrib210l (C1-xy C1-a) (C2-yz (C2-CD-id .C1-e)) (C2-yz (C2-CD-D x)) = refl
distrib210l (C1-xy C1-a) (C2-yz (C2-CD-id .C1-d)) (C2-yz (C2-CD-CD x x₁)) = refl
distrib210l (C1-xy C1-a) (C2-yz (C2-CD-C x)) (C2-yz (C2-CD-id .C1-e)) = refl
distrib210l (C1-xy C1-a) (C2-yz (C2-CD-C x)) (C2-yz (C2-CD-D x₁)) = refl
distrib210l (C1-xy C1-a) (C2-yz (C2-CD-D x)) (C2-yz (C2-CD-id .C1-f)) = refl
distrib210l (C1-xy C1-a) (C2-yz (C2-CD-CD x x₁)) (C2-yz (C2-CD-id .C1-f)) = refl
distrib210l (C1-xy C1-b) (C2-yz (C2-CD-id a)) (C2-yz (C2-CD-id .a)) = refl
distrib210l (C1-xy C1-b) (C2-yz (C2-CD-id .C1-d)) (C2-yz (C2-CD-C x)) = refl
distrib210l (C1-xy C1-b) (C2-yz (C2-CD-id .C1-e)) (C2-yz (C2-CD-D x)) = refl
distrib210l (C1-xy C1-b) (C2-yz (C2-CD-id .C1-d)) (C2-yz (C2-CD-CD x x₁)) = refl
distrib210l (C1-xy C1-b) (C2-yz (C2-CD-C x)) (C2-yz (C2-CD-id .C1-e)) = refl
distrib210l (C1-xy C1-b) (C2-yz (C2-CD-C x)) (C2-yz (C2-CD-D x₁)) = refl
distrib210l (C1-xy C1-b) (C2-yz (C2-CD-D x)) (C2-yz (C2-CD-id .C1-f)) = refl
distrib210l (C1-xy C1-b) (C2-yz (C2-CD-CD x x₁)) (C2-yz (C2-CD-id .C1-f)) = refl
distrib210l (C1-xy C1-c) (C2-yz (C2-CD-id a)) (C2-yz (C2-CD-id .a)) = refl
distrib210l (C1-xy C1-c) (C2-yz (C2-CD-id .C1-d)) (C2-yz (C2-CD-C x)) = refl
distrib210l (C1-xy C1-c) (C2-yz (C2-CD-id .C1-e)) (C2-yz (C2-CD-D x)) = refl
distrib210l (C1-xy C1-c) (C2-yz (C2-CD-id .C1-d)) (C2-yz (C2-CD-CD x x₁)) = refl
distrib210l (C1-xy C1-c) (C2-yz (C2-CD-C x)) (C2-yz (C2-CD-id .C1-e)) = refl
distrib210l (C1-xy C1-c) (C2-yz (C2-CD-C x)) (C2-yz (C2-CD-D x₁)) = refl
distrib210l (C1-xy C1-c) (C2-yz (C2-CD-D x)) (C2-yz (C2-CD-id .C1-f)) = refl
distrib210l (C1-xy C1-c) (C2-yz (C2-CD-CD x x₁)) (C2-yz (C2-CD-id .C1-f)) = refl
distrib210l (C1-yz x) (C2-xx .C0-z) (C2-xx .C0-z) = refl
distrib210l (C1-xz x x₁) (C2-xx .C0-z) (C2-xx .C0-z) = refl

distrib210r : {x y z : C0} {f1 f2 f3 : C1 x y} (u1 : C2 f1 f2) (u2 : C2 f2 f3) (g : C1 y z) → 3PCat.comp20 C (3PCat.comp21 C u1 u2) (3PCat.id1 C g) ≡ 3PCat.comp21 C (3PCat.comp20 C u1 (3PCat.id1 C g)) (3PCat.comp20 C u2 (3PCat.id1 C g))
distrib210r (C2-xx x) (C2-xx .x) (C1-id .x) = refl
distrib210r (C2-xx .C0-x) (C2-xx .C0-x) (C1-xy x) = refl
distrib210r (C2-xx .C0-y) (C2-xx .C0-y) (C1-yz x) = refl
distrib210r (C2-xx .C0-x) (C2-xx .C0-x) (C1-xz x x₁) = refl
distrib210r (C2-xy (C2-AB-id a)) (C2-xy (C2-AB-id .a)) (C1-id .C0-y) = refl
distrib210r (C2-xy (C2-AB-id .C1-a)) (C2-xy (C2-AB-A x)) (C1-id .C0-y) = refl
distrib210r (C2-xy (C2-AB-id .C1-b)) (C2-xy (C2-AB-B x)) (C1-id .C0-y) = refl
distrib210r (C2-xy (C2-AB-id .C1-a)) (C2-xy (C2-AB-AB x x₁)) (C1-id .C0-y) = refl
distrib210r (C2-xy (C2-AB-A x)) (C2-xy (C2-AB-id .C1-b)) (C1-id .C0-y) = refl
distrib210r (C2-xy (C2-AB-A x)) (C2-xy (C2-AB-B x₁)) (C1-id .C0-y) = refl
distrib210r (C2-xy (C2-AB-B x)) (C2-xy (C2-AB-id .C1-c)) (C1-id .C0-y) = refl
distrib210r (C2-xy (C2-AB-AB x x₁)) (C2-xy (C2-AB-id .C1-c)) (C1-id .C0-y) = refl
distrib210r (C2-xy (C2-AB-id a)) (C2-xy (C2-AB-id .a)) (C1-yz x) = refl
distrib210r (C2-xy (C2-AB-id .C1-a)) (C2-xy (C2-AB-A x₁)) (C1-yz x) = refl
distrib210r (C2-xy (C2-AB-id .C1-b)) (C2-xy (C2-AB-B x₁)) (C1-yz x) = refl
distrib210r (C2-xy (C2-AB-id .C1-a)) (C2-xy (C2-AB-AB x₁ x₂)) (C1-yz x) = refl
distrib210r (C2-xy (C2-AB-A x₁)) (C2-xy (C2-AB-id .C1-b)) (C1-yz x) = refl
distrib210r (C2-xy (C2-AB-A x₁)) (C2-xy (C2-AB-B x₂)) (C1-yz x) = refl
distrib210r (C2-xy (C2-AB-B x₁)) (C2-xy (C2-AB-id .C1-c)) (C1-yz x) = refl
distrib210r (C2-xy (C2-AB-AB x₁ x₂)) (C2-xy (C2-AB-id .C1-c)) (C1-yz x) = refl
distrib210r (C2-yz (C2-CD-id a)) (C2-yz (C2-CD-id .a)) (C1-id .C0-z) = refl
distrib210r (C2-yz (C2-CD-id .C1-d)) (C2-yz (C2-CD-C x)) (C1-id .C0-z) = refl
distrib210r (C2-yz (C2-CD-id .C1-e)) (C2-yz (C2-CD-D x)) (C1-id .C0-z) = refl
distrib210r (C2-yz (C2-CD-id .C1-d)) (C2-yz (C2-CD-CD x x₁)) (C1-id .C0-z) = refl
distrib210r (C2-yz (C2-CD-C x)) (C2-yz (C2-CD-id .C1-e)) (C1-id .C0-z) = refl
distrib210r (C2-yz (C2-CD-C x)) (C2-yz (C2-CD-D x₁)) (C1-id .C0-z) = refl
distrib210r (C2-yz (C2-CD-D x)) (C2-yz (C2-CD-id .C1-f)) (C1-id .C0-z) = refl
distrib210r (C2-yz (C2-CD-CD x x₁)) (C2-yz (C2-CD-id .C1-f)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id a) (C2-CD-id a₁)) (C2-xz (C2-AB-id .a) (C2-CD-id .a₁)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id a) (C2-CD-id .C1-d)) (C2-xz (C2-AB-id .a) (C2-CD-C x)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id a) (C2-CD-id .C1-e)) (C2-xz (C2-AB-id .a) (C2-CD-D x)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id a) (C2-CD-id .C1-d)) (C2-xz (C2-AB-id .a) (C2-CD-CD x x₁)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id .C1-a) (C2-CD-id a)) (C2-xz (C2-AB-A x) (C2-CD-id .a)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id .C1-a) (C2-CD-id .C1-d)) (C2-xz (C2-AB-A x) (C2-CD-C x₁)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id .C1-a) (C2-CD-id .C1-e)) (C2-xz (C2-AB-A x) (C2-CD-D x₁)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id .C1-a) (C2-CD-id .C1-d)) (C2-xz (C2-AB-A x) (C2-CD-CD x₁ x₂)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id .C1-b) (C2-CD-id a)) (C2-xz (C2-AB-B x) (C2-CD-id .a)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id .C1-b) (C2-CD-id .C1-d)) (C2-xz (C2-AB-B x) (C2-CD-C x₁)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id .C1-b) (C2-CD-id .C1-e)) (C2-xz (C2-AB-B x) (C2-CD-D x₁)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id .C1-b) (C2-CD-id .C1-d)) (C2-xz (C2-AB-B x) (C2-CD-CD x₁ x₂)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id .C1-a) (C2-CD-id a)) (C2-xz (C2-AB-AB x x₁) (C2-CD-id .a)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id .C1-a) (C2-CD-id .C1-d)) (C2-xz (C2-AB-AB x x₁) (C2-CD-C x₂)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id .C1-a) (C2-CD-id .C1-e)) (C2-xz (C2-AB-AB x x₁) (C2-CD-D x₂)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id .C1-a) (C2-CD-id .C1-d)) (C2-xz (C2-AB-AB x x₁) (C2-CD-CD x₂ x₃)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id a) (C2-CD-C x)) (C2-xz (C2-AB-id .a) (C2-CD-id .C1-e)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id a) (C2-CD-C x)) (C2-xz (C2-AB-id .a) (C2-CD-D x₁)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id .C1-a) (C2-CD-C x)) (C2-xz (C2-AB-A x₁) (C2-CD-id .C1-e)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id .C1-a) (C2-CD-C x)) (C2-xz (C2-AB-A x₁) (C2-CD-D x₂)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id .C1-b) (C2-CD-C x)) (C2-xz (C2-AB-B x₁) (C2-CD-id .C1-e)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id .C1-b) (C2-CD-C x)) (C2-xz (C2-AB-B x₁) (C2-CD-D x₂)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id .C1-a) (C2-CD-C x)) (C2-xz (C2-AB-AB x₁ x₂) (C2-CD-id .C1-e)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id .C1-a) (C2-CD-C x)) (C2-xz (C2-AB-AB x₁ x₂) (C2-CD-D x₃)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id a) (C2-CD-D x)) (C2-xz (C2-AB-id .a) (C2-CD-id .C1-f)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id .C1-a) (C2-CD-D x)) (C2-xz (C2-AB-A x₁) (C2-CD-id .C1-f)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id .C1-b) (C2-CD-D x)) (C2-xz (C2-AB-B x₁) (C2-CD-id .C1-f)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id .C1-a) (C2-CD-D x)) (C2-xz (C2-AB-AB x₁ x₂) (C2-CD-id .C1-f)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id a) (C2-CD-CD x x₁)) (C2-xz (C2-AB-id .a) (C2-CD-id .C1-f)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id .C1-a) (C2-CD-CD x x₁)) (C2-xz (C2-AB-A x₂) (C2-CD-id .C1-f)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id .C1-b) (C2-CD-CD x x₁)) (C2-xz (C2-AB-B x₂) (C2-CD-id .C1-f)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-id .C1-a) (C2-CD-CD x x₁)) (C2-xz (C2-AB-AB x₂ x₃) (C2-CD-id .C1-f)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-A x) (C2-CD-id a)) (C2-xz (C2-AB-id .C1-b) (C2-CD-id .a)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-A x) (C2-CD-id .C1-d)) (C2-xz (C2-AB-id .C1-b) (C2-CD-C x₁)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-A x) (C2-CD-id .C1-e)) (C2-xz (C2-AB-id .C1-b) (C2-CD-D x₁)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-A x) (C2-CD-id .C1-d)) (C2-xz (C2-AB-id .C1-b) (C2-CD-CD x₁ x₂)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-A x) (C2-CD-id a)) (C2-xz (C2-AB-B x₁) (C2-CD-id .a)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-A x) (C2-CD-id .C1-d)) (C2-xz (C2-AB-B x₁) (C2-CD-C x₂)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-A x) (C2-CD-id .C1-e)) (C2-xz (C2-AB-B x₁) (C2-CD-D x₂)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-A x) (C2-CD-id .C1-d)) (C2-xz (C2-AB-B x₁) (C2-CD-CD x₂ x₃)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-A x) (C2-CD-C x₁)) (C2-xz (C2-AB-id .C1-b) (C2-CD-id .C1-e)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-A x) (C2-CD-C x₁)) (C2-xz (C2-AB-id .C1-b) (C2-CD-D x₂)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-A x) (C2-CD-C x₁)) (C2-xz (C2-AB-B x₂) (C2-CD-id .C1-e)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-A x) (C2-CD-C x₁)) (C2-xz (C2-AB-B x₂) (C2-CD-D x₃)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-A x) (C2-CD-D x₁)) (C2-xz (C2-AB-id .C1-b) (C2-CD-id .C1-f)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-A x) (C2-CD-D x₁)) (C2-xz (C2-AB-B x₂) (C2-CD-id .C1-f)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-A x) (C2-CD-CD x₁ x₂)) (C2-xz (C2-AB-id .C1-b) (C2-CD-id .C1-f)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-A x) (C2-CD-CD x₁ x₂)) (C2-xz (C2-AB-B x₃) (C2-CD-id .C1-f)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-B x) (C2-CD-id a)) (C2-xz (C2-AB-id .C1-c) (C2-CD-id .a)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-B x) (C2-CD-id .C1-d)) (C2-xz (C2-AB-id .C1-c) (C2-CD-C x₁)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-B x) (C2-CD-id .C1-e)) (C2-xz (C2-AB-id .C1-c) (C2-CD-D x₁)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-B x) (C2-CD-id .C1-d)) (C2-xz (C2-AB-id .C1-c) (C2-CD-CD x₁ x₂)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-B x) (C2-CD-C x₁)) (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-e)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-B x) (C2-CD-C x₁)) (C2-xz (C2-AB-id .C1-c) (C2-CD-D x₂)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-B x) (C2-CD-D x₁)) (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-f)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-B x) (C2-CD-CD x₁ x₂)) (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-f)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-AB x x₁) (C2-CD-id a)) (C2-xz (C2-AB-id .C1-c) (C2-CD-id .a)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-AB x x₁) (C2-CD-id .C1-d)) (C2-xz (C2-AB-id .C1-c) (C2-CD-C x₂)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-AB x x₁) (C2-CD-id .C1-e)) (C2-xz (C2-AB-id .C1-c) (C2-CD-D x₂)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-AB x x₁) (C2-CD-id .C1-d)) (C2-xz (C2-AB-id .C1-c) (C2-CD-CD x₂ x₃)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-AB x x₁) (C2-CD-C x₂)) (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-e)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-AB x x₁) (C2-CD-C x₂)) (C2-xz (C2-AB-id .C1-c) (C2-CD-D x₃)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-AB x x₁) (C2-CD-D x₂)) (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-f)) (C1-id .C0-z) = refl
distrib210r (C2-xz (C2-AB-AB x x₁) (C2-CD-CD x₂ x₃)) (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-f)) (C1-id .C0-z) = refl

altcomp210 : {x y z : C0} {f1 f2 : C1 x y} {g1 g2 : C1 y z} (u : C2 f1 f2) (v : C2 g1 g2) → 3PCat.comp20 C u v ≡ 3PCat.comp21 C (3PCat.comp20 C u (3PCat.id1 C g1)) (3PCat.comp20 C (3PCat.id1 C f2) v)

altcomp210 (C2-xx x) (C2-xx .x) = refl
altcomp210 (C2-xx .C0-x) (C2-xy A) = refl
altcomp210 (C2-xx .C0-y) (C2-yz A) = refl
altcomp210 (C2-xx .C0-x) (C2-xz A C₁) = refl
altcomp210 (C2-xy (C2-AB-id a)) (C2-xx .C0-y) = refl
altcomp210 (C2-xy (C2-AB-A x)) (C2-xx .C0-y) = refl
altcomp210 (C2-xy (C2-AB-B x)) (C2-xx .C0-y) = refl
altcomp210 (C2-xy (C2-AB-AB x x₁)) (C2-xx .C0-y) = refl
altcomp210 (C2-xy (C2-AB-id a)) (C2-yz (C2-CD-id a₁)) = refl
altcomp210 (C2-xy (C2-AB-id a)) (C2-yz (C2-CD-C x)) = refl
altcomp210 (C2-xy (C2-AB-id a)) (C2-yz (C2-CD-D x)) = refl
altcomp210 (C2-xy (C2-AB-id a)) (C2-yz (C2-CD-CD x x₁)) = refl
altcomp210 (C2-xy (C2-AB-A x)) (C2-yz (C2-CD-id a)) = refl
altcomp210 (C2-xy (C2-AB-A x)) (C2-yz (C2-CD-C x₁)) = refl
altcomp210 (C2-xy (C2-AB-A x)) (C2-yz (C2-CD-D x₁)) = refl
altcomp210 (C2-xy (C2-AB-A x)) (C2-yz (C2-CD-CD x₁ x₂)) = refl
altcomp210 (C2-xy (C2-AB-B x)) (C2-yz (C2-CD-id a)) = refl
altcomp210 (C2-xy (C2-AB-B x)) (C2-yz (C2-CD-C x₁)) = refl
altcomp210 (C2-xy (C2-AB-B x)) (C2-yz (C2-CD-D x₁)) = refl
altcomp210 (C2-xy (C2-AB-B x)) (C2-yz (C2-CD-CD x₁ x₂)) = refl
altcomp210 (C2-xy (C2-AB-AB x x₁)) (C2-yz (C2-CD-id a)) = refl
altcomp210 (C2-xy (C2-AB-AB x x₁)) (C2-yz (C2-CD-C x₂)) = refl
altcomp210 (C2-xy (C2-AB-AB x x₁)) (C2-yz (C2-CD-D x₂)) = refl
altcomp210 (C2-xy (C2-AB-AB x x₁)) (C2-yz (C2-CD-CD x₂ x₃)) = refl
altcomp210 (C2-yz (C2-CD-id a)) (C2-xx .C0-z) = refl
altcomp210 (C2-yz (C2-CD-C x)) (C2-xx .C0-z) = refl
altcomp210 (C2-yz (C2-CD-D x)) (C2-xx .C0-z) = refl
altcomp210 (C2-yz (C2-CD-CD x x₁)) (C2-xx .C0-z) = refl
altcomp210 (C2-xz (C2-AB-id a) (C2-CD-id a₁)) (C2-xx .C0-z) = refl
altcomp210 (C2-xz (C2-AB-id a) (C2-CD-C x)) (C2-xx .C0-z) = refl
altcomp210 (C2-xz (C2-AB-id a) (C2-CD-D x)) (C2-xx .C0-z) = refl
altcomp210 (C2-xz (C2-AB-id a) (C2-CD-CD x x₁)) (C2-xx .C0-z) = refl
altcomp210 (C2-xz (C2-AB-A x) (C2-CD-id a)) (C2-xx .C0-z) = refl
altcomp210 (C2-xz (C2-AB-A x) (C2-CD-C x₁)) (C2-xx .C0-z) = refl
altcomp210 (C2-xz (C2-AB-A x) (C2-CD-D x₁)) (C2-xx .C0-z) = refl
altcomp210 (C2-xz (C2-AB-A x) (C2-CD-CD x₁ x₂)) (C2-xx .C0-z) = refl
altcomp210 (C2-xz (C2-AB-B x) (C2-CD-id a)) (C2-xx .C0-z) = refl
altcomp210 (C2-xz (C2-AB-B x) (C2-CD-C x₁)) (C2-xx .C0-z) = refl
altcomp210 (C2-xz (C2-AB-B x) (C2-CD-D x₁)) (C2-xx .C0-z) = refl
altcomp210 (C2-xz (C2-AB-B x) (C2-CD-CD x₁ x₂)) (C2-xx .C0-z) = refl
altcomp210 (C2-xz (C2-AB-AB x x₁) (C2-CD-id a)) (C2-xx .C0-z) = refl
altcomp210 (C2-xz (C2-AB-AB x x₁) (C2-CD-C x₂)) (C2-xx .C0-z) = refl
altcomp210 (C2-xz (C2-AB-AB x x₁) (C2-CD-D x₂)) (C2-xx .C0-z) = refl
altcomp210 (C2-xz (C2-AB-AB x x₁) (C2-CD-CD x₂ x₃)) (C2-xx .C0-z) = refl

altcomp210' : {x y z : C0} {f1 f2 : C1 x y} {g1 g2 : C1 y z} (u : C2 f1 f2) (v : C2 g1 g2) → 3PCat.comp20 C u v ≡ 3PCat.comp21 C (3PCat.comp20 C (3PCat.id1 C f1) v) (3PCat.comp20 C u (3PCat.id1 C g2) )
altcomp210' (C2-xx x) (C2-xx .x) = refl
altcomp210' (C2-xx .C0-x) (C2-xy (C2-AB-id a)) = refl
altcomp210' (C2-xx .C0-x) (C2-xy (C2-AB-A x)) = refl
altcomp210' (C2-xx .C0-x) (C2-xy (C2-AB-B x)) = refl
altcomp210' (C2-xx .C0-x) (C2-xy (C2-AB-AB x x₁)) = refl
altcomp210' (C2-xx .C0-y) (C2-yz (C2-CD-id a)) = refl
altcomp210' (C2-xx .C0-y) (C2-yz (C2-CD-C x)) = refl
altcomp210' (C2-xx .C0-y) (C2-yz (C2-CD-D x)) = refl
altcomp210' (C2-xx .C0-y) (C2-yz (C2-CD-CD x x₁)) = refl
altcomp210' (C2-xx .C0-x) (C2-xz (C2-AB-id a) (C2-CD-id a₁)) = refl
altcomp210' (C2-xx .C0-x) (C2-xz (C2-AB-id a) (C2-CD-C x)) = refl
altcomp210' (C2-xx .C0-x) (C2-xz (C2-AB-id a) (C2-CD-D x)) = refl
altcomp210' (C2-xx .C0-x) (C2-xz (C2-AB-id a) (C2-CD-CD x x₁)) = refl
altcomp210' (C2-xx .C0-x) (C2-xz (C2-AB-A x) (C2-CD-id a)) = refl
altcomp210' (C2-xx .C0-x) (C2-xz (C2-AB-A x) (C2-CD-C x₁)) = refl
altcomp210' (C2-xx .C0-x) (C2-xz (C2-AB-A x) (C2-CD-D x₁)) = refl
altcomp210' (C2-xx .C0-x) (C2-xz (C2-AB-A x) (C2-CD-CD x₁ x₂)) = refl
altcomp210' (C2-xx .C0-x) (C2-xz (C2-AB-B x) (C2-CD-id a)) = refl
altcomp210' (C2-xx .C0-x) (C2-xz (C2-AB-B x) (C2-CD-C x₁)) = refl
altcomp210' (C2-xx .C0-x) (C2-xz (C2-AB-B x) (C2-CD-D x₁)) = refl
altcomp210' (C2-xx .C0-x) (C2-xz (C2-AB-B x) (C2-CD-CD x₁ x₂)) = refl
altcomp210' (C2-xx .C0-x) (C2-xz (C2-AB-AB x x₁) (C2-CD-id a)) = refl
altcomp210' (C2-xx .C0-x) (C2-xz (C2-AB-AB x x₁) (C2-CD-C x₂)) = refl
altcomp210' (C2-xx .C0-x) (C2-xz (C2-AB-AB x x₁) (C2-CD-D x₂)) = refl
altcomp210' (C2-xx .C0-x) (C2-xz (C2-AB-AB x x₁) (C2-CD-CD x₂ x₃)) = refl
altcomp210' (C2-xy A) (C2-xx .C0-y) = refl
altcomp210' (C2-xy (C2-AB-id a)) (C2-yz (C2-CD-id a₁)) = refl
altcomp210' (C2-xy (C2-AB-id a)) (C2-yz (C2-CD-C x)) = refl
altcomp210' (C2-xy (C2-AB-id a)) (C2-yz (C2-CD-D x)) = refl
altcomp210' (C2-xy (C2-AB-id a)) (C2-yz (C2-CD-CD x x₁)) = refl
altcomp210' (C2-xy (C2-AB-A x)) (C2-yz (C2-CD-id a)) = refl
altcomp210' (C2-xy (C2-AB-A x)) (C2-yz (C2-CD-C x₁)) = refl
altcomp210' (C2-xy (C2-AB-A x)) (C2-yz (C2-CD-D x₁)) = refl
altcomp210' (C2-xy (C2-AB-A x)) (C2-yz (C2-CD-CD x₁ x₂)) = refl
altcomp210' (C2-xy (C2-AB-B x)) (C2-yz (C2-CD-id a)) = refl
altcomp210' (C2-xy (C2-AB-B x)) (C2-yz (C2-CD-C x₁)) = refl
altcomp210' (C2-xy (C2-AB-B x)) (C2-yz (C2-CD-D x₁)) = refl
altcomp210' (C2-xy (C2-AB-B x)) (C2-yz (C2-CD-CD x₁ x₂)) = refl
altcomp210' (C2-xy (C2-AB-AB x x₁)) (C2-yz (C2-CD-id a)) = refl
altcomp210' (C2-xy (C2-AB-AB x x₁)) (C2-yz (C2-CD-C x₂)) = refl
altcomp210' (C2-xy (C2-AB-AB x x₁)) (C2-yz (C2-CD-D x₂)) = refl
altcomp210' (C2-xy (C2-AB-AB x x₁)) (C2-yz (C2-CD-CD x₂ x₃)) = refl
altcomp210' (C2-yz A) (C2-xx .C0-z) = refl
altcomp210' (C2-xz A C₁) (C2-xx .C0-z) = refl

altcomp210'' : {x y z : C0} {f1 f2 : C1 x y} {g1 g2 : C1 y z} (u : C2 f1 f2) (v : C2 g1 g2) → 3PCat.comp21 C (3PCat.comp20 C u (3PCat.id1 C g1)) (3PCat.comp20 C (3PCat.id1 C f2) v) ≡ 3PCat.comp21 C (3PCat.comp20 C (3PCat.id1 C f1) v) (3PCat.comp20 C u (3PCat.id1 C g2))
altcomp210'' u v =
  let p1 = sym (altcomp210 u v) in
  let p2 = altcomp210' u v in
  trans p1 p2

ich210 : is-ich210 C
ich210 {x} {y} {z} {f} {f'} {f''} {g} {g'} {g''} u1 u2 v1 v2 =
  let p = altcomp210 (3PCat.comp21 C u1 u2) (3PCat.comp21 C v1 v2) in
  let p1 = distrib210r u1 u2 g in let p2 = distrib210l f'' v1 v2 in
  let gid = 3PCat.id1 C g in
  let f''id = 3PCat.id1 C f'' in
  let temp1 = 3PCat.comp20 C f''id (3PCat.comp21 C v1 v2) in
  let ctxt1 = λ u → 3PCat.comp21 C u temp1 in
  let p1ext = cong ctxt1 p1 in
  let temp2 = (3PCat.comp21 C (3PCat.comp20 C u1 gid) (3PCat.comp20 C u2 gid)) in let ctxt2 = λ v → 3PCat.comp21 C temp2 v in
  let p2ext = cong ctxt2 p2 in
  let t1 = 3PCat.comp20 C u1 gid in
  let t2 = 3PCat.comp20 C u2 gid in
  let t3 = 3PCat.comp20 C f''id v1 in
  let t4 = 3PCat.comp20 C f''id v2 in
  let p3 = assoc21 t1 t2 (3PCat.comp21 C t3 t4) in
  let p3ext = p3 in
  let p4 = assoc21 t2 t3 t4 in
  let ctxt4 = λ t → 3PCat.comp21 C t1 t in
  let p4ext = sym (cong ctxt4 p4) in
  let p5 = altcomp210'' u2 v1 in
  let ctxt5 = λ t → 3PCat.comp21 C t1 (3PCat.comp21 C t t4) in
  let p5ext = cong ctxt5 p5 in
  
  let f'id = 3PCat.id1 C f' in let g'id = 3PCat.id1 C g' in
  let t2' = 3PCat.comp20 C f'id v1 in let t3' = 3PCat.comp20 C u2 g'id in
  let p6 = assoc21 t2' t3' t4 in
  let ctxt6 = ctxt4 in
  let p6ext = cong ctxt6 p6 in
  
  let p7 = assoc21 t1 t2' (3PCat.comp21 C t3' t4) in
  let p7ext = sym p7 in
  
  let p8 = altcomp210 u1 v1 in
  let ctxt8 = λ p →  3PCat.comp21 C p (3PCat.comp21 C (3PCat.comp20 C u2 (3PCat.id1 C g')) (3PCat.comp20 C (3PCat.id1 C f'') v2)) in
  let p8ext = sym (cong ctxt8 p8) in
  
  let p9 = altcomp210 u2 v2 in
  let ctxt9 = λ t → 3PCat.comp21 C (3PCat.comp20 C u1 v1) t in
  let p9ext = sym (cong ctxt9 p9) in
  let p = trans p p1ext in let p = trans p p2ext in let p = trans p p3ext in let p = trans p p4ext in
  let p = trans p p5ext in let p = trans p p6ext in let p = trans p p7ext in let p = trans p p8ext in
  trans p p9ext

