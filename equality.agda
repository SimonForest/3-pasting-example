
-- Equality lemmas
--
-- authors: Simon Forest and Samuel Mimram

open import Relation.Binary.PropositionalEquality

coe : {A A' : Set} → (A ≡ A') → A → A'
coe refl x = x

cong₃ : {S₁ : Set} {f f' g g' : S₁} (C₂ : S₁ → S₁ → Set) (C₃ : {f g : S₁} → C₂ f g → C₂ f g → Set) {F G : C₂ f g} {F' G' : C₂ f' g'} (pf : f ≡ f') (pg : g ≡ g') (pF : (coe (cong₂ C₂ pf pg) F) ≡ F') → (pG : (coe (cong₂ C₂ pf pg) G) ≡ G') → C₃ F G ≡ C₃ F' G'
cong₃ C2 C3 refl refl refl refl = refl
