
-- Exmple definition
--
-- authors: Simon Forest and Samuel Mimram

open import 3cat

data C0 : Set where
  C0-x : C0
  C0-y : C0
  C0-z : C0

data C1-abc : Set where
  C1-a : C1-abc
  C1-b : C1-abc
  C1-c : C1-abc

data C1-def : Set where
  C1-d : C1-def
  C1-e : C1-def
  C1-f : C1-def

data C1 : C0 → C0 → Set where
  C1-id : (x : C0) → C1 x x
  C1-xy : C1-abc → C1 C0-x C0-y
  C1-yz : C1-def → C1 C0-y C0-z
  C1-xz : C1-abc → C1-def → C1 C0-x C0-z

data C2-AA : Set where
  C2-A : C2-AA
  C2-A' : C2-AA

data C2-BB : Set where
  C2-B : C2-BB
  C2-B' : C2-BB

data C2-CC : Set where
  C2-C : C2-CC
  C2-C' : C2-CC

data C2-DD : Set where
  C2-D : C2-DD
  C2-D' : C2-DD

-- 2-cells from x to y
data C2-AB : C1-abc → C1-abc → Set where
  C2-AB-id : (a : C1-abc) → C2-AB a a
  C2-AB-A : C2-AA → C2-AB C1-a C1-b
  C2-AB-B : C2-BB → C2-AB C1-b C1-c
  C2-AB-AB : C2-AA → C2-BB → C2-AB C1-a C1-c

-- 2-cells from y to z
data C2-CD : C1-def → C1-def → Set where
  C2-CD-id : (a : C1-def) → C2-CD a a
  C2-CD-C : C2-CC → C2-CD C1-d C1-e
  C2-CD-D : C2-DD → C2-CD C1-e C1-f
  C2-CD-CD : C2-CC → C2-DD → C2-CD C1-d C1-f

data C2 : {x y : C0} → (a b : C1 x y) → Set where
  C2-xx : (x : C0) → C2 (C1-id x) (C1-id x)
  C2-xy : {a b : C1-abc} (A : C2-AB a b) → C2 (C1-xy a) (C1-xy b)
  C2-yz : {a b : C1-def} (A : C2-CD a b) → C2 (C1-yz a) (C1-yz b)
  C2-xz : {a b : C1-abc} {c d : C1-def} (A : C2-AB a b) (C : C2-CD c d) → C2 (C1-xz a c) (C1-xz b d)

data C3 : {x y : C0} {a b : C1 x y} (A B : C2 a b) → Set where
  C3-id : {x y : C0} {a b : C1 x y} (A : C2 a b) → C3 A A
  C3-Γ : C3 (C2-xz (C2-AB-A C2-A) (C2-CD-D C2-D)) (C2-xz (C2-AB-A C2-A') (C2-CD-D C2-D'))
  C3-Γ-B : (B : C2-BB) → C3 (C2-xz (C2-AB-AB C2-A B) (C2-CD-D C2-D)) (C2-xz (C2-AB-AB C2-A' B) (C2-CD-D C2-D'))
  C3-Γ-C : (C : C2-CC) → C3 (C2-xz (C2-AB-A C2-A) (C2-CD-CD C C2-D)) (C2-xz (C2-AB-A C2-A') (C2-CD-CD C C2-D'))
  C3-Γ-BC : (B : C2-BB) (C : C2-CC) → C3 (C2-xz (C2-AB-AB C2-A B) (C2-CD-CD C C2-D)) (C2-xz (C2-AB-AB C2-A' B) (C2-CD-CD C C2-D'))
  C3-Θ : C3 (C2-xz (C2-AB-B C2-B) (C2-CD-C C2-C)) (C2-xz (C2-AB-B C2-B') (C2-CD-C C2-C'))
  C3-Θ-A : (A : C2-AA) → C3 (C2-xz (C2-AB-AB A C2-B) (C2-CD-C C2-C)) (C2-xz (C2-AB-AB A C2-B') (C2-CD-C C2-C'))
  C3-Θ-D : (D : C2-DD) → C3 (C2-xz (C2-AB-B C2-B) (C2-CD-CD C2-C D)) (C2-xz (C2-AB-B C2-B') (C2-CD-CD C2-C' D))
  C3-Θ-AD : (A : C2-AA) (D : C2-DD) → C3 (C2-xz (C2-AB-AB A C2-B) (C2-CD-CD C2-C D)) (C2-xz (C2-AB-AB A C2-B') (C2-CD-CD C2-C' D))
  C3-ΓΘ : C3 (C2-xz (C2-AB-AB C2-A C2-B) (C2-CD-CD C2-C C2-D)) (C2-xz (C2-AB-AB C2-A' C2-B') (C2-CD-CD C2-C' C2-D'))
  C3-ΘΓ : C3 (C2-xz (C2-AB-AB C2-A C2-B) (C2-CD-CD C2-C C2-D)) (C2-xz (C2-AB-AB C2-A' C2-B') (C2-CD-CD C2-C' C2-D'))

C : 3PCat C0 C1 C2 C3
3PCat.id0 C x = C1-id x
3PCat.id1 C (C1-id x) = C2-xx x
3PCat.id1 C (C1-xy a) = C2-xy (C2-AB-id a)
3PCat.id1 C (C1-yz d) = C2-yz (C2-CD-id d)
3PCat.id1 C (C1-xz a d) = C2-xz (C2-AB-id a) (C2-CD-id d)
3PCat.id2 C F = C3-id F
3PCat.comp10 C (C1-id x) g = g
3PCat.comp10 C (C1-xy f) (C1-id .C0-y) = C1-xy f
3PCat.comp10 C (C1-xy f) (C1-yz g) = C1-xz f g
3PCat.comp10 C (C1-yz f) (C1-id .C0-z) = C1-yz f
3PCat.comp10 C (C1-xz f g) (C1-id .C0-z) = C1-xz f g
3PCat.comp20 C (C2-xx x) F = F
3PCat.comp20 C (C2-xy A) (C2-xx .C0-y) = C2-xy A
3PCat.comp20 C (C2-xy A) (C2-yz C) = C2-xz A C
3PCat.comp20 C (C2-yz A) (C2-xx .C0-z) = C2-yz A
3PCat.comp20 C (C2-xz A C) (C2-xx .C0-z) = C2-xz A C
3PCat.comp21 C (C2-xx x) G = G
3PCat.comp21 C (C2-xy (C2-AB-id a)) (C2-xy B) = C2-xy B
3PCat.comp21 C (C2-xy (C2-AB-A A)) (C2-xy (C2-AB-id .C1-b)) = C2-xy (C2-AB-A A)
3PCat.comp21 C (C2-xy (C2-AB-A A)) (C2-xy (C2-AB-B B)) = C2-xy (C2-AB-AB A B)
3PCat.comp21 C (C2-xy (C2-AB-B B)) (C2-xy (C2-AB-id .C1-c)) = C2-xy (C2-AB-B B)
3PCat.comp21 C (C2-xy (C2-AB-AB A B)) (C2-xy (C2-AB-id .C1-c)) = C2-xy (C2-AB-AB A B)
3PCat.comp21 C (C2-yz (C2-CD-id a)) (C2-yz A) = C2-yz A
3PCat.comp21 C (C2-yz (C2-CD-C C)) (C2-yz (C2-CD-id .C1-e)) = C2-yz (C2-CD-C C) 
3PCat.comp21 C (C2-yz (C2-CD-C C)) (C2-yz (C2-CD-D D)) = C2-yz (C2-CD-CD C D )
3PCat.comp21 C (C2-yz (C2-CD-D D)) (C2-yz (C2-CD-id .C1-f)) = C2-yz (C2-CD-D D)
3PCat.comp21 C (C2-yz (C2-CD-CD C D)) (C2-yz (C2-CD-id .C1-f)) = C2-yz (C2-CD-CD C D)
3PCat.comp21 C (C2-xz (C2-AB-id a) (C2-CD-id d)) (C2-xz B D) = C2-xz B D
3PCat.comp21 C (C2-xz (C2-AB-id a) (C2-CD-C C)) (C2-xz B (C2-CD-id .C1-e)) = C2-xz B (C2-CD-C C)
3PCat.comp21 C (C2-xz (C2-AB-id a) (C2-CD-C C)) (C2-xz B (C2-CD-D D)) = C2-xz B (C2-CD-CD C D)
3PCat.comp21 C (C2-xz (C2-AB-id a) (C2-CD-D D)) (C2-xz B (C2-CD-id .C1-f)) = C2-xz B (C2-CD-D D)
3PCat.comp21 C (C2-xz (C2-AB-id a) (C2-CD-CD C D)) (C2-xz B (C2-CD-id .C1-f)) = C2-xz B (C2-CD-CD C D)
3PCat.comp21 C (C2-xz (C2-AB-A A) (C2-CD-id a)) (C2-xz (C2-AB-id .C1-b) D) = C2-xz (C2-AB-A A) D
3PCat.comp21 C (C2-xz (C2-AB-A A) (C2-CD-id a)) (C2-xz (C2-AB-B B) D) = C2-xz (C2-AB-AB A B) D
3PCat.comp21 C (C2-xz (C2-AB-A A) (C2-CD-C C)) (C2-xz (C2-AB-id .C1-b) (C2-CD-id .C1-e)) = C2-xz (C2-AB-A A) (C2-CD-C C) 
3PCat.comp21 C (C2-xz (C2-AB-A A) (C2-CD-C C)) (C2-xz (C2-AB-id .C1-b) (C2-CD-D D)) = C2-xz (C2-AB-A A) (C2-CD-CD C D)
3PCat.comp21 C (C2-xz (C2-AB-A A) (C2-CD-C C)) (C2-xz (C2-AB-B B) (C2-CD-id .C1-e)) = C2-xz (C2-AB-AB A B) (C2-CD-C C)
3PCat.comp21 C (C2-xz (C2-AB-A A) (C2-CD-C C)) (C2-xz (C2-AB-B B) (C2-CD-D D)) = C2-xz (C2-AB-AB A B) (C2-CD-CD C D)
3PCat.comp21 C (C2-xz (C2-AB-A A) (C2-CD-D D)) (C2-xz (C2-AB-id .C1-b) (C2-CD-id .C1-f)) = C2-xz (C2-AB-A A) (C2-CD-D D)
3PCat.comp21 C (C2-xz (C2-AB-A A) (C2-CD-D D)) (C2-xz (C2-AB-B B) (C2-CD-id .C1-f)) = C2-xz (C2-AB-AB A B) (C2-CD-D D)
3PCat.comp21 C (C2-xz (C2-AB-A A) (C2-CD-CD C D)) (C2-xz (C2-AB-id .C1-b) (C2-CD-id .C1-f)) = C2-xz (C2-AB-A A) (C2-CD-CD C D)
3PCat.comp21 C (C2-xz (C2-AB-A A) (C2-CD-CD C D)) (C2-xz (C2-AB-B B) (C2-CD-id .C1-f)) = C2-xz (C2-AB-AB A B) (C2-CD-CD C D) 
3PCat.comp21 C (C2-xz (C2-AB-B B) (C2-CD-id a)) (C2-xz (C2-AB-id .C1-c) C) = C2-xz (C2-AB-B B) C
3PCat.comp21 C (C2-xz (C2-AB-B B) (C2-CD-C C)) (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-e)) = C2-xz (C2-AB-B B) (C2-CD-C C)
3PCat.comp21 C (C2-xz (C2-AB-B B) (C2-CD-C C)) (C2-xz (C2-AB-id .C1-c) (C2-CD-D D)) = C2-xz (C2-AB-B B) (C2-CD-CD C D)
3PCat.comp21 C (C2-xz (C2-AB-B B) (C2-CD-D D)) (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-f)) = C2-xz (C2-AB-B B) (C2-CD-D D)
3PCat.comp21 C (C2-xz (C2-AB-B B) (C2-CD-CD C D)) (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-f)) = C2-xz (C2-AB-B B) (C2-CD-CD C D)
3PCat.comp21 C (C2-xz (C2-AB-AB A B) (C2-CD-id a)) (C2-xz (C2-AB-id .C1-c) C) = C2-xz (C2-AB-AB A B) C
3PCat.comp21 C (C2-xz (C2-AB-AB A B) (C2-CD-C C)) (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-e)) = C2-xz (C2-AB-AB A B) (C2-CD-C C)
3PCat.comp21 C (C2-xz (C2-AB-AB A B) (C2-CD-C C)) (C2-xz (C2-AB-id .C1-c) (C2-CD-D D)) = C2-xz (C2-AB-AB A B) (C2-CD-CD C D) 
3PCat.comp21 C (C2-xz (C2-AB-AB A B) (C2-CD-D D)) (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-f)) = C2-xz (C2-AB-AB A B) (C2-CD-D D)
3PCat.comp21 C (C2-xz (C2-AB-AB A B) (C2-CD-CD C D)) (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-f)) = C2-xz (C2-AB-AB A B) (C2-CD-CD C D)
3PCat.comp30 C (C3-id A) (C3-id B) = C3-id (3PCat.comp20 C A B)
3PCat.comp30 C (C3-id (C2-xx .C0-x)) C3-Γ = C3-Γ
3PCat.comp30 C (C3-id (C2-xx .C0-x)) (C3-Γ-B B) = C3-Γ-B B
3PCat.comp30 C (C3-id (C2-xx .C0-x)) (C3-Γ-C C) = C3-Γ-C C
3PCat.comp30 C (C3-id (C2-xx .C0-x)) (C3-Γ-BC B C) = C3-Γ-BC B C
3PCat.comp30 C (C3-id (C2-xx .C0-x)) C3-Θ = C3-Θ
3PCat.comp30 C (C3-id (C2-xx .C0-x)) (C3-Θ-A A) = C3-Θ-A A
3PCat.comp30 C (C3-id (C2-xx .C0-x)) (C3-Θ-D D) = C3-Θ-D D
3PCat.comp30 C (C3-id (C2-xx .C0-x)) (C3-Θ-AD A D) = C3-Θ-AD A D
3PCat.comp30 C C3-Γ (C3-id (C2-xx .C0-z)) = C3-Γ
3PCat.comp30 C (C3-Γ-B B) (C3-id (C2-xx .C0-z)) = C3-Γ-B B
3PCat.comp30 C (C3-Γ-C C) (C3-id (C2-xx .C0-z)) = C3-Γ-C C
3PCat.comp30 C (C3-Γ-BC B C) (C3-id (C2-xx .C0-z)) = C3-Γ-BC B C
3PCat.comp30 C C3-Θ (C3-id (C2-xx .C0-z)) = C3-Θ
3PCat.comp30 C (C3-Θ-A A) (C3-id (C2-xx .C0-z)) = C3-Θ-A A
3PCat.comp30 C (C3-Θ-D D) (C3-id (C2-xx .C0-z)) = C3-Θ-D D
3PCat.comp30 C (C3-Θ-AD A D) (C3-id (C2-xx .C0-z)) = C3-Θ-AD A D
3PCat.comp30 C C3-ΓΘ (C3-id (C2-xx .C0-z)) = C3-ΓΘ
3PCat.comp30 C (C3-id (C2-xx .C0-x)) C3-ΓΘ = C3-ΓΘ
3PCat.comp30 C (C3-id (C2-xx .C0-x)) C3-ΘΓ = C3-ΘΓ
3PCat.comp30 C C3-ΘΓ (C3-id (C2-xx .C0-z)) = C3-ΘΓ
3PCat.comp31 C (C3-id (C2-xx x)) (C3-id B) = C3-id B
3PCat.comp31 C (C3-id (C2-xy (C2-AB-id a))) (C3-id (C2-xy A)) = C3-id (C2-xy A)
3PCat.comp31 C (C3-id (C2-xy (C2-AB-A A))) (C3-id (C2-xy (C2-AB-id .C1-b))) = C3-id (C2-xy (C2-AB-A A))
3PCat.comp31 C (C3-id (C2-xy (C2-AB-A A))) (C3-id (C2-xy (C2-AB-B B))) = C3-id (C2-xy (C2-AB-AB A B))
3PCat.comp31 C (C3-id (C2-xy (C2-AB-B B))) (C3-id (C2-xy (C2-AB-id .C1-c))) = C3-id (C2-xy (C2-AB-B B))
3PCat.comp31 C (C3-id (C2-xy (C2-AB-AB A B))) (C3-id (C2-xy (C2-AB-id .C1-c))) = C3-id (C2-xy (C2-AB-AB A B))
3PCat.comp31 C (C3-id (C2-yz (C2-CD-id a))) (C3-id (C2-yz A)) = C3-id (C2-yz A)
3PCat.comp31 C (C3-id (C2-yz (C2-CD-C C))) (C3-id (C2-yz (C2-CD-id .C1-e))) = C3-id (C2-yz (C2-CD-C C))
3PCat.comp31 C (C3-id (C2-yz (C2-CD-C C))) (C3-id (C2-yz (C2-CD-D D))) = C3-id (C2-yz (C2-CD-CD C D))
3PCat.comp31 C (C3-id (C2-yz (C2-CD-D D))) (C3-id (C2-yz (C2-CD-id .C1-f))) = C3-id (C2-yz (C2-CD-D D))
3PCat.comp31 C (C3-id (C2-yz (C2-CD-CD C D))) (C3-id (C2-yz (C2-CD-id .C1-f))) = C3-id (C2-yz (C2-CD-CD C D))
3PCat.comp31 C (C3-id (C2-xz (C2-AB-id a) (C2-CD-id .d))) (C3-id (C2-xz B (C2-CD-id d))) = C3-id (C2-xz B (C2-CD-id d))
3PCat.comp31 C (C3-id (C2-xz (C2-AB-id a) (C2-CD-C C))) (C3-id (C2-xz B (C2-CD-id .C1-e))) = C3-id (C2-xz B (C2-CD-C C))
3PCat.comp31 C (C3-id (C2-xz (C2-AB-id a) (C2-CD-D D))) (C3-id (C2-xz B (C2-CD-id .C1-f))) = C3-id (C2-xz B (C2-CD-D D))
3PCat.comp31 C (C3-id (C2-xz (C2-AB-id a) (C2-CD-CD C D))) (C3-id (C2-xz B (C2-CD-id .C1-f))) = C3-id (C2-xz B (C2-CD-CD C D))
3PCat.comp31 C (C3-id (C2-xz (C2-AB-id a) (C2-CD-id .C1-d))) (C3-id (C2-xz B (C2-CD-C C))) = C3-id (C2-xz B (C2-CD-C C))
3PCat.comp31 C (C3-id (C2-xz (C2-AB-id a) (C2-CD-id .C1-e))) (C3-id (C2-xz B (C2-CD-D D))) = C3-id (C2-xz B (C2-CD-D D))
3PCat.comp31 C (C3-id (C2-xz (C2-AB-id a) (C2-CD-C C))) (C3-id (C2-xz B (C2-CD-D D))) = C3-id (C2-xz B (C2-CD-CD C D))
3PCat.comp31 C (C3-id (C2-xz (C2-AB-id a) (C2-CD-id .C1-d))) (C3-id (C2-xz B (C2-CD-CD C D))) = C3-id (C2-xz B (C2-CD-CD C D))
3PCat.comp31 C (C3-id (C2-xz (C2-AB-A A) (C2-CD-id a))) (C3-id (C2-xz (C2-AB-id .C1-b) D)) = C3-id (C2-xz (C2-AB-A A) D)
3PCat.comp31 C (C3-id (C2-xz (C2-AB-A A) (C2-CD-C C))) (C3-id (C2-xz (C2-AB-id .C1-b) (C2-CD-id .C1-e))) = C3-id (C2-xz (C2-AB-A A) (C2-CD-C C))
3PCat.comp31 C (C3-id (C2-xz (C2-AB-A A) (C2-CD-C C))) (C3-id (C2-xz (C2-AB-id .C1-b) (C2-CD-D D))) = C3-id (C2-xz (C2-AB-A A) (C2-CD-CD C D))
3PCat.comp31 C (C3-id (C2-xz (C2-AB-A A) (C2-CD-D D))) (C3-id (C2-xz (C2-AB-id .C1-b) (C2-CD-id .C1-f))) = C3-id (C2-xz (C2-AB-A A) (C2-CD-D D))
3PCat.comp31 C (C3-id (C2-xz (C2-AB-A A) (C2-CD-CD C D))) (C3-id (C2-xz (C2-AB-id .C1-b) (C2-CD-id .C1-f))) = C3-id (C2-xz (C2-AB-A A) (C2-CD-CD C D)) 
3PCat.comp31 C (C3-id (C2-xz (C2-AB-A A) (C2-CD-id a))) (C3-id (C2-xz (C2-AB-B B) D)) = C3-id (C2-xz (C2-AB-AB A B) D)
3PCat.comp31 C (C3-id (C2-xz (C2-AB-A A) (C2-CD-C C))) (C3-id (C2-xz (C2-AB-B B) (C2-CD-id .C1-e))) = C3-id (C2-xz (C2-AB-AB A B) (C2-CD-C C))
3PCat.comp31 C (C3-id (C2-xz (C2-AB-A A) (C2-CD-C C))) (C3-id (C2-xz (C2-AB-B B) (C2-CD-D D))) = C3-id (C2-xz (C2-AB-AB A B) (C2-CD-CD C D))
3PCat.comp31 C (C3-id (C2-xz (C2-AB-A A) (C2-CD-D D))) (C3-id (C2-xz (C2-AB-B B) (C2-CD-id .C1-f))) = C3-id (C2-xz (C2-AB-AB A B) (C2-CD-D D))
3PCat.comp31 C (C3-id (C2-xz (C2-AB-A A) (C2-CD-CD C D))) (C3-id (C2-xz (C2-AB-B B) (C2-CD-id .C1-f))) = C3-id (C2-xz (C2-AB-AB A B) (C2-CD-CD C D))
3PCat.comp31 C (C3-id (C2-xz (C2-AB-B B) (C2-CD-id a))) (C3-id (C2-xz (C2-AB-id .C1-c) D)) = C3-id (C2-xz (C2-AB-B B) D)
3PCat.comp31 C (C3-id (C2-xz (C2-AB-B B) (C2-CD-C C))) (C3-id (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-e))) = C3-id (C2-xz (C2-AB-B B) (C2-CD-C C))
3PCat.comp31 C (C3-id (C2-xz (C2-AB-B B) (C2-CD-C C))) (C3-id (C2-xz (C2-AB-id .C1-c) (C2-CD-D D))) = C3-id (C2-xz (C2-AB-B B) (C2-CD-CD C D))
3PCat.comp31 C (C3-id (C2-xz (C2-AB-B B) (C2-CD-D D))) (C3-id (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-f))) = C3-id (C2-xz (C2-AB-B B) (C2-CD-D D))
3PCat.comp31 C (C3-id (C2-xz (C2-AB-B B) (C2-CD-CD C D))) (C3-id (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-f))) = C3-id (C2-xz (C2-AB-B B) (C2-CD-CD C D))
3PCat.comp31 C (C3-id (C2-xz (C2-AB-AB A B) (C2-CD-id a))) (C3-id (C2-xz (C2-AB-id .C1-c) D)) = C3-id (C2-xz (C2-AB-AB A B) D)
3PCat.comp31 C (C3-id (C2-xz (C2-AB-AB A B) (C2-CD-C C))) (C3-id (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-e))) = C3-id (C2-xz (C2-AB-AB A B) (C2-CD-C C))
3PCat.comp31 C (C3-id (C2-xz (C2-AB-AB A B) (C2-CD-C C))) (C3-id (C2-xz (C2-AB-id .C1-c) (C2-CD-D D))) = C3-id (C2-xz (C2-AB-AB A B) (C2-CD-CD C D))
3PCat.comp31 C (C3-id (C2-xz (C2-AB-AB A B) (C2-CD-D D))) (C3-id (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-f))) = C3-id (C2-xz (C2-AB-AB A B) (C2-CD-D D))
3PCat.comp31 C (C3-id (C2-xz (C2-AB-AB A B) (C2-CD-CD C D))) (C3-id (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-f))) = C3-id (C2-xz (C2-AB-AB A B) (C2-CD-CD C D))
3PCat.comp31 C (C3-id (C2-xz (C2-AB-id .C1-a) (C2-CD-id .C1-e))) C3-Γ = C3-Γ
3PCat.comp31 C (C3-id (C2-xz (C2-AB-id .C1-a) (C2-CD-C C))) C3-Γ = C3-Γ-C C
3PCat.comp31 C (C3-id (C2-xz (C2-AB-id .C1-a) (C2-CD-id .C1-e))) (C3-Γ-B B) = C3-Γ-B B
3PCat.comp31 C (C3-id (C2-xz (C2-AB-id .C1-a) (C2-CD-C C))) (C3-Γ-B B) = C3-Γ-BC B C
3PCat.comp31 C (C3-id (C2-xz (C2-AB-id .C1-a) (C2-CD-id .C1-d))) (C3-Γ-C C) = C3-Γ-C C
3PCat.comp31 C (C3-id (C2-xz (C2-AB-id .C1-a) (C2-CD-id .C1-d))) (C3-Γ-BC B C) = C3-Γ-BC B C
3PCat.comp31 C (C3-id (C2-xz (C2-AB-id .C1-b) (C2-CD-id .C1-d))) C3-Θ = C3-Θ
3PCat.comp31 C (C3-id (C2-xz (C2-AB-A A) (C2-CD-id .C1-d))) C3-Θ = C3-Θ-A A
3PCat.comp31 C (C3-id (C2-xz (C2-AB-id .C1-a) (C2-CD-id .C1-d))) (C3-Θ-A A) = C3-Θ-A A
3PCat.comp31 C (C3-id (C2-xz (C2-AB-id .C1-b) (C2-CD-id .C1-d))) (C3-Θ-D D) = C3-Θ-D D
3PCat.comp31 C (C3-id (C2-xz (C2-AB-A A) (C2-CD-id .C1-d))) (C3-Θ-D D) = C3-Θ-AD A D
3PCat.comp31 C (C3-id (C2-xz (C2-AB-id .C1-a) (C2-CD-id .C1-d))) (C3-Θ-AD A D) = C3-Θ-AD A D
3PCat.comp31 C C3-Γ (C3-id (C2-xz (C2-AB-id .C1-b) (C2-CD-id .C1-f))) = C3-Γ
3PCat.comp31 C C3-Γ (C3-id (C2-xz (C2-AB-B B) (C2-CD-id .C1-f))) = C3-Γ-B B
3PCat.comp31 C (C3-Γ-B B) (C3-id (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-f))) = C3-Γ-B B
3PCat.comp31 C (C3-Γ-C C) (C3-id (C2-xz (C2-AB-id .C1-b) (C2-CD-id .C1-f))) = C3-Γ-C C
3PCat.comp31 C (C3-Γ-C C) (C3-id (C2-xz (C2-AB-B B) (C2-CD-id .C1-f))) = C3-Γ-BC B C
3PCat.comp31 C (C3-Γ-BC B C) (C3-id (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-f))) = C3-Γ-BC B C
3PCat.comp31 C C3-Θ (C3-id (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-e))) = C3-Θ
3PCat.comp31 C C3-Θ (C3-id (C2-xz (C2-AB-id .C1-c) (C2-CD-D D))) = C3-Θ-D D
3PCat.comp31 C (C3-Θ-A A) (C3-id (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-e))) = C3-Θ-A A
3PCat.comp31 C (C3-Θ-A A) (C3-id (C2-xz (C2-AB-id .C1-c) (C2-CD-D D))) = C3-Θ-AD A D
3PCat.comp31 C (C3-Θ-D D) (C3-id (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-f))) = C3-Θ-D D
3PCat.comp31 C (C3-Θ-AD A D) (C3-id (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-f))) = C3-Θ-AD A D
3PCat.comp31 C C3-ΓΘ (C3-id (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-f))) = C3-ΓΘ
3PCat.comp31 C C3-ΘΓ (C3-id (C2-xz (C2-AB-id .C1-c) (C2-CD-id .C1-f))) = C3-ΘΓ
3PCat.comp31 C (C3-id (C2-xz (C2-AB-id .C1-a) (C2-CD-id .C1-d))) C3-ΓΘ = C3-ΓΘ
3PCat.comp31 C (C3-id (C2-xz (C2-AB-id .C1-a) (C2-CD-id .C1-d))) C3-ΘΓ = C3-ΘΓ
3PCat.comp32 C (C3-id A) ψ = ψ
3PCat.comp32 C C3-Γ (C3-id .(C2-xz (C2-AB-A C2-A') (C2-CD-D C2-D'))) = C3-Γ
3PCat.comp32 C (C3-Γ-B B) (C3-id .(C2-xz (C2-AB-AB C2-A' B) (C2-CD-D C2-D'))) = C3-Γ-B B
3PCat.comp32 C (C3-Γ-C C) (C3-id .(C2-xz (C2-AB-A C2-A') (C2-CD-CD C C2-D'))) = C3-Γ-C C
3PCat.comp32 C (C3-Γ-BC B C) (C3-id .(C2-xz (C2-AB-AB C2-A' B) (C2-CD-CD C C2-D'))) = C3-Γ-BC B C
3PCat.comp32 C (C3-Γ-BC B C) (C3-Θ-AD .C2-A' .C2-D') = C3-ΓΘ
3PCat.comp32 C C3-Θ (C3-id .(C2-xz (C2-AB-B C2-B') (C2-CD-C C2-C'))) = C3-Θ
3PCat.comp32 C (C3-Θ-A A) (C3-id .(C2-xz (C2-AB-AB A C2-B') (C2-CD-C C2-C'))) = C3-Θ-A A
3PCat.comp32 C (C3-Θ-D D) (C3-id .(C2-xz (C2-AB-B C2-B') (C2-CD-CD C2-C' D))) = C3-Θ-D D
3PCat.comp32 C (C3-Θ-AD A D) (C3-id .(C2-xz (C2-AB-AB A C2-B') (C2-CD-CD C2-C' D))) = C3-Θ-AD A D
3PCat.comp32 C (C3-Θ-AD .C2-A .C2-D) (C3-Γ-BC .C2-B' .C2-C') = C3-ΘΓ
3PCat.comp32 C C3-ΓΘ (C3-id .(C2-xz (C2-AB-AB C2-A' C2-B') (C2-CD-CD C2-C' C2-D'))) = C3-ΓΘ
3PCat.comp32 C C3-ΘΓ (C3-id .(C2-xz (C2-AB-AB C2-A' C2-B') (C2-CD-CD C2-C' C2-D'))) = C3-ΘΓ
