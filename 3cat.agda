
-- 3-categories definition
--
-- authors: Simon Forest and Samuel Mimram


-- {-# OPTIONS --rewriting #-}
-- {-# BUILTIN REWRITE _≡_ #-}

open import Relation.Binary.PropositionalEquality
open import equality

module 3cat where

-- 3-precategories : identities and compositions without axioms

record 3PCat
       (C : Set)
  (_→₁_ : (x y : C) → Set)
  (_→₂_ : {x y : C} (f g : x →₁ y) → Set)
  (_→₃_ : {x y : C} {f g : x →₁ y} (F G : f →₂ g) → Set)
  :
  Set
  where
  field
    id0 : (x : C) → x →₁ x
    id1 : {x y : C} (f : x →₁ y) → f →₂ f
    id2 : {x y : C} {f g : x →₁ y} (F : f →₂ g) → F →₃ F

    comp10 : {x y z : C} (f : x →₁ y) (g : y →₁ z) → x →₁ z
    comp20 : {x y z : C} {f f' : x →₁ y} {g g' : y →₁ z} (F : f →₂ f') (G : g →₂ g') → (comp10 f g) →₂ (comp10 f' g')
    comp21 : {x y : C} {f f' f'' : x →₁ y} (F : f →₂ f') (G : f' →₂ f'') → f →₂ f''
    comp30 : {x y z : C} {f f' : x →₁ y} {g g' : y →₁ z} {F F' : f →₂ f'} {G G' : g →₂ g'} (φ : F →₃ F') (ψ : G →₃ G') → (comp20 F G) →₃ (comp20 F' G')
    comp31 : {x y : C} {f f' f'' : x →₁ y} {F F' : f →₂ f'} {G G' : f' →₂ f''} (φ : F →₃ F') (ψ : G →₃ G') → (comp21 F G) →₃ (comp21 F' G')
    comp32 :  {x y : C} {f f' : x →₁ y} {F F' F'' : f →₂ f'} (φ : F →₃ F') (ψ : F' →₃ F'') → F →₃ F''

-- the axioms of a 3-category

module _ 
  {C : Set}
  {_→₁_ : (x y : C) → Set}
  {_→₂_ : {x y : C} (f g : x →₁ y) → Set}
  {_→₃_ : {x y : C} {f g : x →₁ y} (F G : f →₂ g) → Set}
  (PC : 3PCat C _→₁_ _→₂_ _→₃_)
  where
    is-unit10-l : Set
    is-unit10-l = {x y : C} {f : x →₁ y} → 3PCat.comp10 PC (3PCat.id0 PC x) f ≡ f
    is-unit10-r : Set
    is-unit10-r = {x y : C} (f : x →₁ y) → 3PCat.comp10 PC f (3PCat.id0 PC y) ≡ f
    is-unit20-l : (unit10-l : is-unit10-l) → Set
    is-unit20-l unit10-l = {x y : C} {f f' : x →₁ y} {F : f →₂ f'} → coe (cong₂ _→₂_ unit10-l unit10-l) (3PCat.comp20 PC (3PCat.id1 PC (3PCat.id0 PC x)) F) ≡ F
    is-unit20-r : (unit10-r : is-unit10-r) → Set
    is-unit20-r unit10-r = {x y : C} {f f' : x →₁ y} {F : f →₂ f'} → coe (cong₂ _→₂_ (unit10-r f) (unit10-r f')) (3PCat.comp20 PC F (3PCat.id1 PC (3PCat.id0 PC y))) ≡ F
    is-unit21-l : Set
    is-unit21-l = {x y : C} {f f' : x →₁ y} {F : f →₂ f'} → 3PCat.comp21 PC (3PCat.id1 PC f) F ≡ F
    is-unit21-r : Set
    is-unit21-r = {x y : C} {f f' : x →₁ y} {F : f →₂ f'} → 3PCat.comp21 PC F (3PCat.id1 PC f') ≡ F
    is-unit30-l : (unit10-l : is-unit10-l) → (unit20-l : is-unit20-l unit10-l) → Set
    is-unit30-l unit10-l unit20-l = {x y : C} {f f' : x →₁ y} {F F' : f →₂ f'} {φ : F →₃ F'} → coe (cong₃ _→₂_ _→₃_ unit10-l unit10-l unit20-l unit20-l) (3PCat.comp30 PC (3PCat.id2 PC (3PCat.id1 PC (3PCat.id0 PC x))) φ) ≡ φ
    is-unit30-r : (unit10-r : is-unit10-r) → (unit20-r : is-unit20-r unit10-r) → Set
    is-unit30-r unit10-r unit20-r = {x y : C} {f f' : x →₁ y} {F F' : f →₂ f'} {φ : F →₃ F'} → coe (cong₃ _→₂_ _→₃_ (unit10-r f) (unit10-r f') unit20-r unit20-r) (3PCat.comp30 PC φ (3PCat.id2 PC (3PCat.id1 PC (3PCat.id0 PC y)))) ≡ φ
    is-unit31-l : (unit21-l : is-unit21-l) → Set
    is-unit31-l unit21-l = {x y : C} {f f' : x →₁ y} {F F' : f →₂ f'} {φ : F →₃ F'} → coe (cong₂ _→₃_ unit21-l unit21-l) (3PCat.comp31 PC (3PCat.id2 PC (3PCat.id1 PC f)) φ) ≡ φ
    is-unit31-r : (unit21-r : is-unit21-r) → Set
    is-unit31-r unit21-r = {x y : C} {f f' : x →₁ y} {F F' : f →₂ f'} {φ : F →₃ F'} → coe (cong₂ _→₃_ unit21-r unit21-r) (3PCat.comp31 PC φ (3PCat.id2 PC (3PCat.id1 PC f'))) ≡ φ
    is-unit32-l : Set
    is-unit32-l = {x y : C} {f f' : x →₁ y} {F F' : f →₂ f'} {φ : F →₃ F'} → 3PCat.comp32 PC (3PCat.id2 PC F) φ ≡ φ
    is-unit32-r : Set
    is-unit32-r = {x y : C} {f f' : x →₁ y} {F F' : f →₂ f'} {φ : F →₃ F'} → 3PCat.comp32 PC φ (3PCat.id2 PC F') ≡ φ
    is-assoc10 : Set
    is-assoc10 = {x y z w : C} (f : x →₁ y) (g : y →₁ z) (h : z →₁ w) → 3PCat.comp10 PC (3PCat.comp10 PC f g) h ≡ 3PCat.comp10 PC f (3PCat.comp10 PC g h)
    is-assoc20 : (assoc10 : is-assoc10) → Set
    is-assoc20 assoc10 = {x y z w : C} {f f' : x →₁ y} {g g' : y →₁ z} {h h' : z →₁ w} (F : f →₂ f') (G : g →₂ g') (H : h →₂ h') → coe (cong₂ _→₂_ (assoc10 f g h) (assoc10 f' g' h')) (3PCat.comp20 PC (3PCat.comp20 PC F G) H) ≡ 3PCat.comp20 PC F (3PCat.comp20 PC G H)
    is-assoc21 : Set
    is-assoc21 = {x y : C} {f f' f'' f''' : x →₁ y} (F : f →₂ f') (G : f' →₂ f'') (H : f'' →₂ f''') → 3PCat.comp21 PC (3PCat.comp21 PC F G) H ≡ 3PCat.comp21 PC F (3PCat.comp21 PC G H)
    is-assoc30 : (assoc10 : is-assoc10) → (assoc20 : is-assoc20 assoc10) → Set
    is-assoc30 assoc10 assoc20 = {x y z w : C} {f f' : x →₁ y} {g g' : y →₁ z} {h h' : z →₁ w} {F F' : f →₂ f'} {G G' : g →₂ g'} {H H' : h →₂ h'} (φ : F →₃ F') (γ : G →₃ G') (η : H →₃ H') → coe (cong₃ _→₂_ _→₃_ (assoc10 f g h) (assoc10 f' g' h') (assoc20 F G H) (assoc20 F' G' H') ) (3PCat.comp30 PC (3PCat.comp30 PC φ γ) η) ≡ 3PCat.comp30 PC φ (3PCat.comp30 PC γ η)
    is-assoc31 : (assoc21 : is-assoc21) → Set
    is-assoc31 assoc21 = {x y : C} {f f' f'' f''' : x →₁ y} {F F' : f →₂ f'} {G G' : f' →₂ f''} {H H' : f'' →₂ f'''} (φ : F →₃ F') (γ : G →₃ G') (η : H →₃ H') → coe (cong₂ _→₃_ (assoc21 F G H) (assoc21 F' G' H')) (3PCat.comp31 PC (3PCat.comp31 PC φ γ) η) ≡ 3PCat.comp31 PC φ (3PCat.comp31 PC γ η)
    is-assoc32 : Set
    is-assoc32 = {x y : C} {f f' : x →₁ y} {F F' F'' F''' : f →₂ f'} (φ : F →₃ F') (γ : F' →₃ F'') (η : F'' →₃ F''') → 3PCat.comp32 PC (3PCat.comp32 PC φ γ) η ≡ 3PCat.comp32 PC φ (3PCat.comp32 PC γ η)
    is-comp10-id : Set
    is-comp10-id = {x y z : C} (f : x →₁ y) (g : y →₁ z) → 3PCat.id1 PC (3PCat.comp10 PC f g) ≡ 3PCat.comp20 PC (3PCat.id1 PC f) (3PCat.id1 PC g)
    is-comp20-id : Set
    is-comp20-id = {x y z : C} {f f' : x →₁ y} {g g' : y →₁ z} (F : f →₂ f') (G : g →₂ g') → 3PCat.id2 PC (3PCat.comp20 PC F G) ≡ 3PCat.comp30 PC (3PCat.id2 PC F) (3PCat.id2 PC G)
    is-comp21-id : Set
    is-comp21-id = {x y : C} {f f' f'' : x →₁ y} (F : f →₂ f') (G : f' →₂ f'') → 3PCat.id2 PC (3PCat.comp21 PC F G) ≡ 3PCat.comp31 PC (3PCat.id2 PC F) (3PCat.id2 PC G)
    is-ich210 : Set
    is-ich210 = {x y z : C} {f f' f'' : x →₁ y} {g g' g'' : y →₁ z} (F : f →₂ f') (F' : f' →₂ f'') (G : g →₂ g') (G' : g' →₂ g'') → 3PCat.comp20 PC (3PCat.comp21 PC F F') (3PCat.comp21 PC G G') ≡ 3PCat.comp21 PC (3PCat.comp20 PC F G) (3PCat.comp20 PC F' G')
    is-ich310 : (ich210 : is-ich210) → Set
    is-ich310 ich210 = {x y z : C} {f f' f'' : x →₁ y} {g g' g'' : y →₁ z} {F1 F2 : f →₂ f'} {F1' F2' : f' →₂ f''} {G1 G2 : g →₂ g'} {G1' G2' : g' →₂ g''} (φ : F1 →₃ F2) (φ' : F1' →₃ F2') (γ : G1 →₃ G2) (γ' : G1' →₃ G2') → coe (cong₂ _→₃_ (ich210 F1 F1' G1 G1') (ich210 F2 F2' G2 G2')) (3PCat.comp30 PC (3PCat.comp31 PC φ φ') (3PCat.comp31 PC γ γ')) ≡ 3PCat.comp31 PC (3PCat.comp30 PC φ γ) (3PCat.comp30 PC φ' γ')
    is-ich320 : Set
    is-ich320 = {x y z : C} {f f' : x →₁ y} {g g' : y →₁ z} {F1 F2 F3 : f →₂ f'} {G1 G2 G3 : g →₂ g'} (φ : F1 →₃ F2) (φ' : F2 →₃ F3) (γ : G1 →₃ G2) (γ' : G2 →₃ G3) → 3PCat.comp30 PC (3PCat.comp32 PC φ φ') (3PCat.comp32 PC γ γ') ≡ 3PCat.comp32 PC (3PCat.comp30 PC φ γ) (3PCat.comp30 PC φ' γ')
    is-ich321 : Set
    is-ich321 = {x y : C} {f f' f'' : x →₁ y} {F F' F'' : f →₂ f'} {G G' G'' : f' →₂ f''} (φ : F →₃ F') (φ' : F' →₃ F'') (γ : G →₃ G') (γ' : G' →₃ G'') → 3PCat.comp31 PC (3PCat.comp32 PC φ φ') (3PCat.comp32 PC γ γ') ≡ 3PCat.comp32 PC (3PCat.comp31 PC φ γ) (3PCat.comp31 PC φ' γ')


-- 3-category : a 3-precategory that satisfies all the axioms above

record 3Cat
  {C : Set}
  {_→₁_ : (x y : C) → Set}
  {_→₂_ : {x y : C} (f g : x →₁ y) → Set}
  {_→₃_ : {x y : C} {f g : x →₁ y} (F G : f →₂ g) → Set}
  (PC : 3PCat C _→₁_ _→₂_ _→₃_)
  :
  Set
  where
  field
    unit10-l : is-unit10-l PC
    unit10-r : is-unit10-r PC
    unit20-l : is-unit20-l PC unit10-l
    unit20-r : is-unit20-r PC unit10-r
    unit21-l : is-unit21-l PC
    unit21-r : is-unit21-r PC
    unit30-l : is-unit30-l PC unit10-l unit20-l
    unit30-r : is-unit30-r PC unit10-r unit20-r
    unit31-l : is-unit31-l PC unit21-l
    unit31-r : is-unit31-r PC unit21-r
    unit32-l : is-unit32-l PC
    unit32-r : is-unit32-r PC
    assoc10 : is-assoc10 PC
    assoc20 : is-assoc20 PC assoc10
    assoc21 : is-assoc21 PC
    assoc30 : is-assoc30 PC assoc10 assoc20
    assoc31 : is-assoc31 PC assoc21
    assoc32 : is-assoc32 PC
    comp10-id : is-comp10-id PC
    comp20-id : is-comp20-id PC
    comp21-id : is-comp21-id PC
    ich210 : is-ich210 PC
    ich310 : is-ich310 PC ich210
    ich320 : is-ich320 PC
    ich321 : is-ich321 PC
