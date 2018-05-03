
-- proofs about units
--
-- authors: Simon Forest and Samuel Mimram

open import Agda.Builtin.Equality
open import 3cat
open import ex

unit10-l : is-unit10-l C
unit10-l = refl

unit10-r : is-unit10-r C
unit10-r (C1-id x) = refl
unit10-r (C1-xy x) = refl
unit10-r (C1-yz x) = refl
unit10-r (C1-xz x x₁) = refl

unit20-l : is-unit20-l C unit10-l
unit20-l = refl

unit20-r : is-unit20-r C unit10-r
unit20-r {F = C2-xx x} = refl
unit20-r {F = C2-xy A} = refl
unit20-r {F = C2-yz A} = refl
unit20-r {F = C2-xz A C} = refl

unit21-l : is-unit21-l C
unit21-l {F = C2-xx x} = refl
unit21-l {F = C2-xy A} = refl
unit21-l {F = C2-yz A} = refl
unit21-l {F = C2-xz A C₁} = refl

unit21-r : is-unit21-r C
unit21-r {F = C2-xx x} = refl
unit21-r {F = C2-xy (C2-AB-id a)} = refl
unit21-r {F = C2-xy (C2-AB-A A)} = refl
unit21-r {F = C2-xy (C2-AB-B B)} = refl
unit21-r {F = C2-xy (C2-AB-AB A B)} = refl
unit21-r {F = C2-yz (C2-CD-id a)} = refl
unit21-r {F = C2-yz (C2-CD-C C)} = refl
unit21-r {F = C2-yz (C2-CD-D D)} = refl
unit21-r {F = C2-yz (C2-CD-CD C D)} = refl
unit21-r {F = C2-xz (C2-AB-id a) (C2-CD-id a₁)} = refl
unit21-r {F = C2-xz (C2-AB-id a) (C2-CD-C x)} = refl
unit21-r {F = C2-xz (C2-AB-id a) (C2-CD-D x)} = refl
unit21-r {F = C2-xz (C2-AB-id a) (C2-CD-CD x x₁)} = refl
unit21-r {F = C2-xz (C2-AB-A x) (C2-CD-id a)} = refl
unit21-r {F = C2-xz (C2-AB-A x) (C2-CD-C x₁)} = refl
unit21-r {F = C2-xz (C2-AB-A x) (C2-CD-D x₁)} = refl
unit21-r {F = C2-xz (C2-AB-A x) (C2-CD-CD x₁ x₂)} = refl
unit21-r {F = C2-xz (C2-AB-B x) (C2-CD-id a)} = refl
unit21-r {F = C2-xz (C2-AB-B x) (C2-CD-C x₁)} = refl
unit21-r {F = C2-xz (C2-AB-B x) (C2-CD-D x₁)} = refl
unit21-r {F = C2-xz (C2-AB-B x) (C2-CD-CD x₁ x₂)} = refl
unit21-r {F = C2-xz (C2-AB-AB x x₁) (C2-CD-id a)} = refl
unit21-r {F = C2-xz (C2-AB-AB x x₁) (C2-CD-C x₂)} = refl
unit21-r {F = C2-xz (C2-AB-AB x x₁) (C2-CD-D x₂)} = refl
unit21-r {F = C2-xz (C2-AB-AB x x₁) (C2-CD-CD x₂ x₃)} = refl

unit30-l : is-unit30-l C unit10-l unit20-l
unit30-l {φ = C3-id A} = refl
unit30-l {φ = C3-Γ} = refl
unit30-l {φ = C3-Γ-B B} = refl
unit30-l {φ = C3-Γ-C C₁} = refl
unit30-l {φ = C3-Γ-BC B C₁} = refl
unit30-l {φ = C3-Θ} = refl
unit30-l {φ = C3-Θ-A A} = refl
unit30-l {φ = C3-Θ-D D} = refl
unit30-l {φ = C3-Θ-AD A D} = refl
unit30-l {φ = C3-ΓΘ} = refl
unit30-l {φ = C3-ΘΓ} = refl

unit30-r : is-unit30-r C unit10-r unit20-r
unit30-r {φ = C3-id (C2-xx x)} = refl
unit30-r {φ = C3-id (C2-xy A)} = refl
unit30-r {φ = C3-id (C2-yz A)} = refl
unit30-r {φ = C3-id (C2-xz A C₁)} = refl
unit30-r {φ = C3-Γ} = refl
unit30-r {φ = C3-Γ-B B} = refl
unit30-r {φ = C3-Γ-C C₁} = refl
unit30-r {φ = C3-Γ-BC B C₁} = refl
unit30-r {φ = C3-Θ} = refl
unit30-r {φ = C3-Θ-A A} = refl
unit30-r {φ = C3-Θ-D D} = refl
unit30-r {φ = C3-Θ-AD A D} = refl
unit30-r {φ = C3-ΓΘ} = refl
unit30-r {φ = C3-ΘΓ} = refl

unit31-l : is-unit31-l C unit21-l
unit31-l {φ = C3-id (C2-xx x)} = refl
unit31-l {φ = C3-id (C2-xy A)} = refl
unit31-l {φ = C3-id (C2-yz A)} = refl
unit31-l {φ = C3-id (C2-xz A (C2-CD-id a))} = refl
unit31-l {φ = C3-id (C2-xz A (C2-CD-C x))} = refl
unit31-l {φ = C3-id (C2-xz A (C2-CD-D x))} = refl
unit31-l {φ = C3-id (C2-xz A (C2-CD-CD x x₁))} = refl
unit31-l {φ = C3-Γ} = refl
unit31-l {φ = C3-Γ-B B} = refl
unit31-l {φ = C3-Γ-C C₁} = refl
unit31-l {φ = C3-Γ-BC B C₁} = refl
unit31-l {φ = C3-Θ} = refl
unit31-l {φ = C3-Θ-A A} = refl
unit31-l {φ = C3-Θ-D D} = refl
unit31-l {φ = C3-Θ-AD A D} = refl
unit31-l {φ = C3-ΓΘ} = refl
unit31-l {φ = C3-ΘΓ} = refl

unit31-r : is-unit31-r C unit21-r
unit31-r {φ = C3-id (C2-xx x)} = refl
unit31-r {φ = C3-id (C2-xy (C2-AB-id a))} = refl
unit31-r {φ = C3-id (C2-xy (C2-AB-A A))} = refl
unit31-r {φ = C3-id (C2-xy (C2-AB-B B))} = refl
unit31-r {φ = C3-id (C2-xy (C2-AB-AB A B))} = refl
unit31-r {φ = C3-id (C2-yz (C2-CD-id a))} = refl
unit31-r {φ = C3-id (C2-yz (C2-CD-C C))} = refl
unit31-r {φ = C3-id (C2-yz (C2-CD-D D))} = refl
unit31-r {φ = C3-id (C2-yz (C2-CD-CD C D))} = refl
unit31-r {φ = C3-id (C2-xz (C2-AB-id a) (C2-CD-id a₁))} = refl
unit31-r {φ = C3-id (C2-xz (C2-AB-id a) (C2-CD-C C))} = refl
unit31-r {φ = C3-id (C2-xz (C2-AB-id a) (C2-CD-D D))} = refl
unit31-r {φ = C3-id (C2-xz (C2-AB-id a) (C2-CD-CD C D))} = refl
unit31-r {φ = C3-id (C2-xz (C2-AB-A A) (C2-CD-id a))} = refl
unit31-r {φ = C3-id (C2-xz (C2-AB-A A) (C2-CD-C C))} = refl
unit31-r {φ = C3-id (C2-xz (C2-AB-A A) (C2-CD-D D))} = refl
unit31-r {φ = C3-id (C2-xz (C2-AB-A A) (C2-CD-CD C D))} = refl
unit31-r {φ = C3-id (C2-xz (C2-AB-B B) (C2-CD-id a))} = refl
unit31-r {φ = C3-id (C2-xz (C2-AB-B B) (C2-CD-C C))} = refl
unit31-r {φ = C3-id (C2-xz (C2-AB-B B) (C2-CD-D C))} = refl
unit31-r {φ = C3-id (C2-xz (C2-AB-B B) (C2-CD-CD C D))} = refl
unit31-r {φ = C3-id (C2-xz (C2-AB-AB A B) (C2-CD-id a))} = refl
unit31-r {φ = C3-id (C2-xz (C2-AB-AB A B) (C2-CD-C C))} = refl
unit31-r {φ = C3-id (C2-xz (C2-AB-AB A B) (C2-CD-D C))} = refl
unit31-r {φ = C3-id (C2-xz (C2-AB-AB A B) (C2-CD-CD C D))} = refl
unit31-r {φ = C3-Γ} = refl
unit31-r {φ = C3-Γ-B B} = refl
unit31-r {φ = C3-Γ-C C₁} = refl
unit31-r {φ = C3-Γ-BC B C₁} = refl
unit31-r {φ = C3-Θ} = refl
unit31-r {φ = C3-Θ-A A} = refl
unit31-r {φ = C3-Θ-D D} = refl
unit31-r {φ = C3-Θ-AD A D} = refl
unit31-r {φ = C3-ΓΘ} = refl
unit31-r {φ = C3-ΘΓ} = refl

unit32-l : is-unit32-l C
unit32-l {φ = C3-id A} = refl
unit32-l {φ = C3-Γ} = refl
unit32-l {φ = C3-Γ-B B} = refl
unit32-l {φ = C3-Γ-C C₁} = refl
unit32-l {φ = C3-Γ-BC B C₁} = refl
unit32-l {φ = C3-Θ} = refl
unit32-l {φ = C3-Θ-A A} = refl
unit32-l {φ = C3-Θ-D D} = refl
unit32-l {φ = C3-Θ-AD A D} = refl
unit32-l {φ = C3-ΓΘ} = refl
unit32-l {φ = C3-ΘΓ} = refl

unit32-r : is-unit32-r C
unit32-r {φ = C3-id A} = refl
unit32-r {φ = C3-Γ} = refl
unit32-r {φ = C3-Γ-B B} = refl
unit32-r {φ = C3-Γ-C C₁} = refl
unit32-r {φ = C3-Γ-BC B C₁} = refl
unit32-r {φ = C3-Θ} = refl
unit32-r {φ = C3-Θ-A A} = refl
unit32-r {φ = C3-Θ-D D} = refl
unit32-r {φ = C3-Θ-AD A D} = refl
unit32-r {φ = C3-ΓΘ} = refl
unit32-r {φ = C3-ΘΓ} = refl
