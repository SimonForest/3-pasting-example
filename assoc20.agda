
-- (2,0)-associativity proof
--
-- authors: Simon Forest and Samuel Mimram

open import Agda.Builtin.Equality
open import 3cat
open import assoc10
open import ex

assoc20 : is-assoc20 C assoc10
assoc20 (C2-xx x) G H = refl
assoc20 (C2-xy A) (C2-xx .C0-y) H = refl
assoc20 (C2-xy (C2-AB-id a)) (C2-yz (C2-CD-id a₁)) (C2-xx .C0-z) = refl
assoc20 (C2-xy (C2-AB-id a)) (C2-yz (C2-CD-C C)) (C2-xx .C0-z) = refl
assoc20 (C2-xy (C2-AB-id a)) (C2-yz (C2-CD-D D)) (C2-xx .C0-z) = refl
assoc20 (C2-xy (C2-AB-id a)) (C2-yz (C2-CD-CD C D)) (C2-xx .C0-z) = refl
assoc20 (C2-xy (C2-AB-A A)) (C2-yz (C2-CD-id a)) (C2-xx .C0-z) = refl
assoc20 (C2-xy (C2-AB-A A)) (C2-yz (C2-CD-C C)) (C2-xx .C0-z) = refl
assoc20 (C2-xy (C2-AB-A A)) (C2-yz (C2-CD-D D)) (C2-xx .C0-z) = refl
assoc20 (C2-xy (C2-AB-A A)) (C2-yz (C2-CD-CD C D)) (C2-xx .C0-z) = refl
assoc20 (C2-xy (C2-AB-B B)) (C2-yz (C2-CD-id a)) (C2-xx .C0-z) = refl
assoc20 (C2-xy (C2-AB-B B)) (C2-yz (C2-CD-C C)) (C2-xx .C0-z) = refl
assoc20 (C2-xy (C2-AB-B B)) (C2-yz (C2-CD-D D)) (C2-xx .C0-z) = refl
assoc20 (C2-xy (C2-AB-B B)) (C2-yz (C2-CD-CD C D)) (C2-xx .C0-z) = refl
assoc20 (C2-xy (C2-AB-AB A B)) (C2-yz (C2-CD-id a)) (C2-xx .C0-z) = refl
assoc20 (C2-xy (C2-AB-AB A B)) (C2-yz (C2-CD-C C)) (C2-xx .C0-z) = refl
assoc20 (C2-xy (C2-AB-AB A B)) (C2-yz (C2-CD-D D)) (C2-xx .C0-z) = refl
assoc20 (C2-xy (C2-AB-AB A B)) (C2-yz (C2-CD-CD C d)) (C2-xx .C0-z) = refl
assoc20 (C2-yz (C2-CD-id a)) (C2-xx .C0-z) H = refl
assoc20 (C2-yz (C2-CD-C C)) (C2-xx .C0-z) H = refl
assoc20 (C2-yz (C2-CD-D D)) (C2-xx .C0-z) H = refl
assoc20 (C2-yz (C2-CD-CD C D)) (C2-xx .C0-z) H = refl
assoc20 (C2-xz A C) (C2-xx .C0-z) H = refl
