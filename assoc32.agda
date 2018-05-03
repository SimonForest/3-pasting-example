
-- (3,2)-associativity proof
--
-- authors: Simon Forest and Samuel Mimram

open import Agda.Builtin.Equality
open import 3cat
open import ex

assoc32 : is-assoc32 C
assoc32 (C3-id A) γ η = refl
assoc32 C3-Γ (C3-id .(C2-xz (C2-AB-A C2-A') (C2-CD-D C2-D'))) η = refl
assoc32 (C3-Γ-B B) (C3-id .(C2-xz (C2-AB-AB C2-A' B) (C2-CD-D C2-D'))) η = refl
assoc32 (C3-Γ-C C₁) (C3-id .(C2-xz (C2-AB-A C2-A') (C2-CD-CD C₁ C2-D'))) η = refl
assoc32 (C3-Γ-BC B C₁) (C3-id .(C2-xz (C2-AB-AB C2-A' B) (C2-CD-CD C₁ C2-D'))) η = refl
assoc32 (C3-Γ-BC .C2-B .C2-C) (C3-Θ-AD .C2-A' .C2-D') (C3-id .(C2-xz (C2-AB-AB C2-A' C2-B') (C2-CD-CD C2-C' C2-D'))) = refl
assoc32 C3-Θ (C3-id .(C2-xz (C2-AB-B C2-B') (C2-CD-C C2-C'))) η = refl
assoc32 (C3-Θ-A A) (C3-id .(C2-xz (C2-AB-AB A C2-B') (C2-CD-C C2-C'))) η = refl
assoc32 (C3-Θ-D D) (C3-id .(C2-xz (C2-AB-B C2-B') (C2-CD-CD C2-C' D))) η = refl
assoc32 (C3-Θ-AD A D) (C3-id .(C2-xz (C2-AB-AB A C2-B') (C2-CD-CD C2-C' D))) η = refl
assoc32 (C3-Θ-AD .C2-A .C2-D) (C3-Γ-BC .C2-B' .C2-C') (C3-id .(C2-xz (C2-AB-AB C2-A' C2-B') (C2-CD-CD C2-C' C2-D'))) = refl
assoc32 C3-ΓΘ (C3-id .(C2-xz (C2-AB-AB C2-A' C2-B') (C2-CD-CD C2-C' C2-D'))) η = refl
assoc32 C3-ΘΓ (C3-id .(C2-xz (C2-AB-AB C2-A' C2-B') (C2-CD-CD C2-C' C2-D'))) η = refl
