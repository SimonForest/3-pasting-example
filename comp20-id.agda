
-- (2,0)-compatibility between compositions and identities proof
--
-- authors: Simon Forest and Samuel Mimram

open import Agda.Builtin.Equality
open import 3cat
open import ex

comp20-id : is-comp20-id C
comp20-id (C2-xx x) G = refl
comp20-id (C2-xy A) G = refl
comp20-id (C2-yz A) G = refl
comp20-id (C2-xz A C₁) G = refl
