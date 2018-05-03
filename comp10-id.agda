
-- (1,0)-compatibility between compositions and identities proof
--
-- authors: Simon Forest and Samuel Mimram


open import Agda.Builtin.Equality
open import 3cat
open import ex

comp10-id : is-comp10-id C
comp10-id (C1-id x) g = refl
comp10-id (C1-xy x) (C1-id .C0-y) = refl
comp10-id (C1-xy x) (C1-yz x₁) = refl
comp10-id (C1-yz x) (C1-id .C0-z) = refl
comp10-id (C1-xz x x₁) (C1-id .C0-z) = refl
