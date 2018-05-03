
-- (2,1)-compatibility between compositions and identities proof
--
-- authors: Simon Forest and Samuel Mimram

open import Agda.Builtin.Equality
open import 3cat
open import ex

comp21-id : is-comp21-id C
comp21-id (C2-xx x) G = refl
comp21-id (C2-xy (C2-AB-id a)) (C2-xy A₁) = refl
comp21-id (C2-xy (C2-AB-A x)) (C2-xy (C2-AB-id .C1-b)) = refl
comp21-id (C2-xy (C2-AB-A x)) (C2-xy (C2-AB-B x₁)) = refl
comp21-id (C2-xy (C2-AB-B x)) (C2-xy (C2-AB-id .C1-c)) = refl
comp21-id (C2-xy (C2-AB-AB x x₁)) (C2-xy (C2-AB-id .C1-c)) = refl
comp21-id (C2-yz (C2-CD-id a)) (C2-yz A) = refl
comp21-id (C2-yz (C2-CD-C x)) (C2-yz (C2-CD-id .C1-e)) = refl
comp21-id (C2-yz (C2-CD-C x)) (C2-yz (C2-CD-D x₁)) = refl
comp21-id (C2-yz (C2-CD-D x)) (C2-yz (C2-CD-id .C1-f)) = refl
comp21-id (C2-yz (C2-CD-CD x x₁)) (C2-yz (C2-CD-id .C1-f)) = refl
comp21-id (C2-xz (C2-AB-id a) (C2-CD-id a₁)) (C2-xz (C2-AB-id .a) (C2-CD-id .a₁)) = refl
comp21-id (C2-xz (C2-AB-id a) (C2-CD-id .C1-d)) (C2-xz (C2-AB-id .a) (C2-CD-C x)) = refl
comp21-id (C2-xz (C2-AB-id a) (C2-CD-id .C1-e)) (C2-xz (C2-AB-id .a) (C2-CD-D x)) = refl
comp21-id (C2-xz (C2-AB-id a) (C2-CD-id .C1-d)) (C2-xz (C2-AB-id .a) (C2-CD-CD x x₁)) = refl 
comp21-id (C2-xz (C2-AB-id .C1-a) (C2-CD-id a₁)) (C2-xz (C2-AB-A x) (C2-CD-id .a₁)) = refl
comp21-id (C2-xz (C2-AB-id .C1-a) (C2-CD-id .C1-d)) (C2-xz (C2-AB-A x) (C2-CD-C x₁)) = refl
comp21-id (C2-xz (C2-AB-id .C1-a) (C2-CD-id .C1-e)) (C2-xz (C2-AB-A x) (C2-CD-D x₁)) = refl
comp21-id (C2-xz (C2-AB-id .C1-a) (C2-CD-id .C1-d)) (C2-xz (C2-AB-A x) (C2-CD-CD x₁ x₂)) = refl
comp21-id (C2-xz (C2-AB-id .C1-b) (C2-CD-id a₁)) (C2-xz (C2-AB-B x) (C2-CD-id .a₁)) = refl
comp21-id (C2-xz (C2-AB-id .C1-b) (C2-CD-id .C1-d)) (C2-xz (C2-AB-B x) (C2-CD-C x₁)) = refl
comp21-id (C2-xz (C2-AB-id .C1-b) (C2-CD-id .C1-e)) (C2-xz (C2-AB-B x) (C2-CD-D x₁)) = refl
comp21-id (C2-xz (C2-AB-id .C1-b) (C2-CD-id .C1-d)) (C2-xz (C2-AB-B x) (C2-CD-CD x₁ x₂)) = refl
comp21-id (C2-xz (C2-AB-id .C1-a) (C2-CD-id a₁)) (C2-xz (C2-AB-AB x x₁) (C2-CD-id .a₁)) = refl
comp21-id (C2-xz (C2-AB-id .C1-a) (C2-CD-id .C1-d)) (C2-xz (C2-AB-AB x x₁) (C2-CD-C x₂)) = refl
comp21-id (C2-xz (C2-AB-id .C1-a) (C2-CD-id .C1-e)) (C2-xz (C2-AB-AB x x₁) (C2-CD-D x₂)) = refl
comp21-id (C2-xz (C2-AB-id .C1-a) (C2-CD-id .C1-d)) (C2-xz (C2-AB-AB x x₁) (C2-CD-CD x₂ x₃)) = refl
comp21-id (C2-xz (C2-AB-id a) (C2-CD-C x)) (C2-xz (C2-AB-id .a) (C2-CD-id .C1-e)) = refl
comp21-id (C2-xz (C2-AB-id a) (C2-CD-C x)) (C2-xz (C2-AB-id .a) (C2-CD-D x₁)) = refl
comp21-id (C2-xz (C2-AB-id .C1-a) (C2-CD-C x)) (C2-xz (C2-AB-A x₁) (C2-CD-id .C1-e)) = refl
comp21-id (C2-xz (C2-AB-id .C1-a) (C2-CD-C x)) (C2-xz (C2-AB-A x₁) (C2-CD-D x₂)) = refl
comp21-id (C2-xz (C2-AB-id .C1-b) (C2-CD-C x)) (C2-xz (C2-AB-B x₁) (C2-CD-id .C1-e)) = refl
comp21-id (C2-xz (C2-AB-id .C1-b) (C2-CD-C x)) (C2-xz (C2-AB-B x₁) (C2-CD-D x₂)) = refl
comp21-id (C2-xz (C2-AB-id .C1-a) (C2-CD-C x)) (C2-xz (C2-AB-AB x₁ x₂) (C2-CD-id .C1-e)) = refl
comp21-id (C2-xz (C2-AB-id .C1-a) (C2-CD-C x)) (C2-xz (C2-AB-AB x₁ x₂) (C2-CD-D x₃)) = refl
comp21-id (C2-xz (C2-AB-id a) (C2-CD-D x)) (C2-xz (C2-AB-id .a) (C2-CD-id .C1-f)) = refl
comp21-id (C2-xz (C2-AB-id .C1-a) (C2-CD-D x)) (C2-xz (C2-AB-A x₁) (C2-CD-id .C1-f)) = refl
comp21-id (C2-xz (C2-AB-id .C1-b) (C2-CD-D x)) (C2-xz (C2-AB-B x₁) (C2-CD-id .C1-f)) = refl
comp21-id (C2-xz (C2-AB-id .C1-a) (C2-CD-D x)) (C2-xz (C2-AB-AB x₁ x₂) (C2-CD-id .C1-f)) = refl
comp21-id (C2-xz (C2-AB-id a) (C2-CD-CD x x₁)) (C2-xz (C2-AB-id .a) (C2-CD-id .C1-f)) = refl
comp21-id (C2-xz (C2-AB-id .C1-a) (C2-CD-CD x x₁)) (C2-xz (C2-AB-A x₂) (C2-CD-id .C1-f)) = refl
comp21-id (C2-xz (C2-AB-id .C1-b) (C2-CD-CD x x₁)) (C2-xz (C2-AB-B x₂) (C2-CD-id .C1-f)) = refl
comp21-id (C2-xz (C2-AB-id .C1-a) (C2-CD-CD x x₁)) (C2-xz (C2-AB-AB x₂ x₃) (C2-CD-id .C1-f)) = refl
comp21-id (C2-xz (C2-AB-A x) (C2-CD-id a)) (C2-xz (C2-AB-id .C1-b) C₁) = refl
comp21-id (C2-xz (C2-AB-A x) (C2-CD-id a)) (C2-xz (C2-AB-B x₁) C₁) = refl
comp21-id (C2-xz (C2-AB-A x) (C2-CD-C x₁)) (C2-xz (C2-AB-id .C1-b) (C2-CD-id .C1-e)) = refl
comp21-id (C2-xz (C2-AB-A x) (C2-CD-C x₁)) (C2-xz (C2-AB-id .C1-b) (C2-CD-D x₂)) = refl
comp21-id (C2-xz (C2-AB-A x) (C2-CD-C x₁)) (C2-xz (C2-AB-B x₂) (C2-CD-id .C1-e)) = refl
comp21-id (C2-xz (C2-AB-A x) (C2-CD-C x₁)) (C2-xz (C2-AB-B x₂) (C2-CD-D x₃)) = refl
comp21-id (C2-xz (C2-AB-A x) (C2-CD-D x₁)) (C2-xz (C2-AB-id .C1-b) (C2-CD-id .C1-f)) = refl
comp21-id (C2-xz (C2-AB-A x) (C2-CD-D x₁)) (C2-xz (C2-AB-B x₂) (C2-CD-id .C1-f)) = refl
comp21-id (C2-xz (C2-AB-A x) (C2-CD-CD x₁ x₂)) (C2-xz (C2-AB-id .C1-b) (C2-CD-id .C1-f)) = refl
comp21-id (C2-xz (C2-AB-A x) (C2-CD-CD x₁ x₂)) (C2-xz (C2-AB-B x₃) (C2-CD-id .C1-f)) = refl
comp21-id (C2-xz (C2-AB-B x) (C2-CD-id a)) (C2-xz (C2-AB-id .C1-c) (C2-CD-id .a)) = refl
comp21-id (C2-xz (C2-AB-B x) (C2-CD-id .C1-d)) (C2-xz (C2-AB-id .C1-c) (C2-CD-C x₁)) = refl
comp21-id (C2-xz (C2-AB-B x) (C2-CD-id .C1-e)) (C2-xz (C2-AB-id .C1-c) (C2-CD-D x₁)) = refl
comp21-id (C2-xz (C2-AB-B x) (C2-CD-id .C1-d)) (C2-xz (C2-AB-id .C1-c) (C2-CD-CD x₁ x₂)) = refl
comp21-id (C2-xz (C2-AB-B x) (C2-CD-C x₁)) (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-e)) = refl
comp21-id (C2-xz (C2-AB-B x) (C2-CD-C x₁)) (C2-xz (C2-AB-id .C1-c) (C2-CD-D x₂)) = refl
comp21-id (C2-xz (C2-AB-B x) (C2-CD-D x₁)) (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-f)) = refl
comp21-id (C2-xz (C2-AB-B x) (C2-CD-CD x₁ x₂)) (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-f)) = refl
comp21-id (C2-xz (C2-AB-AB x x₁) (C2-CD-id a)) (C2-xz (C2-AB-id .C1-c) (C2-CD-id .a)) = refl
comp21-id (C2-xz (C2-AB-AB x x₁) (C2-CD-id .C1-d)) (C2-xz (C2-AB-id .C1-c) (C2-CD-C x₂)) = refl
comp21-id (C2-xz (C2-AB-AB x x₁) (C2-CD-id .C1-e)) (C2-xz (C2-AB-id .C1-c) (C2-CD-D x₂)) = refl
comp21-id (C2-xz (C2-AB-AB x x₁) (C2-CD-id .C1-d)) (C2-xz (C2-AB-id .C1-c) (C2-CD-CD x₂ x₃)) = refl
comp21-id (C2-xz (C2-AB-AB x x₁) (C2-CD-C x₂)) (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-e)) = refl
comp21-id (C2-xz (C2-AB-AB x x₁) (C2-CD-C x₂)) (C2-xz (C2-AB-id .C1-c) (C2-CD-D x₃)) = refl
comp21-id (C2-xz (C2-AB-AB x x₁) (C2-CD-D x₂)) (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-f)) = refl
comp21-id (C2-xz (C2-AB-AB x x₁) (C2-CD-CD x₂ x₃)) (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-f)) = refl
