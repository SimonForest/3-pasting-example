
-- (1,0)-associativity proof
--
-- authors: Simon Forest and Samuel Mimram

open import Agda.Builtin.Equality
open import 3cat
open import ex


assoc10 : is-assoc10 C
assoc10 (C1-id x) g h = refl
assoc10 (C1-xy x) (C1-id .C0-y) h = refl
assoc10 (C1-xy x) (C1-yz x₁) (C1-id .C0-z) = refl
assoc10 (C1-yz x) (C1-id .C0-z) h = refl
assoc10 (C1-xz x x₁) (C1-id .C0-z) h = refl
