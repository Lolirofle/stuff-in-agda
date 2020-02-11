module Sets.IterativeSet where

import      Lvl
open import Data
open import Data.Boolean
open import Data.Boolean.Stmt
open import Data.Either as Either using (_‖_)
open import Data.Tuple as Tuple using ()
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Relator.Equals using () renaming (_≡_ to Id ; [≡]-intro to intro)
open import Syntax.Function
open import Type
open import Type.Dependent

module _ where
  private variable {ℓ₁ ℓ₂} : Lvl.Level

  -- A model of constructive set theory (CZF) using iterative sets. (TODO: Not sure. Filter does not work?)
  record Iset : Type{Lvl.𝐒(ℓ₁)} where
    coinductive
    constructor intro
    field
      {Index} : Type{ℓ₁}
      elem : Index → Iset{ℓ₁}
  open Iset

{- TODO: Neither provable or unprovable?
  Iset-no-eta-identity1 : ∀{A : Iset{ℓ₁}} → ¬(Id A (intro(elem A)))
  Iset-no-eta-identity1 {A = _} ()

  Iset-no-eta-identity2 : ∀{I : Type{ℓ₁}}{e : I → Iset{ℓ₁}} → ¬(Id (Iset.intro{Index = I}(e)) (Iset.intro{Index = I}(e)))
  Iset-no-eta-identity2 ()
-}

  ∅ : Iset{ℓ₁}
  ∅ = intro{Index = Empty} empty

  singleton : Iset{ℓ₁} → Iset{ℓ₁}
  singleton = intro{Index = Unit} ∘ const

  pair : Iset{ℓ₁} → Iset{ℓ₁} → Iset{ℓ₁}
  pair A B = intro{Index = Lvl.Up(Bool)} \{(Lvl.up 𝐹) → A ; (Lvl.up 𝑇) → B}

  _∪_ : Iset{ℓ₁} → Iset{ℓ₁} → Iset{ℓ₁}
  A ∪ B = intro{Index = Index(A) ‖ Index(B)} (Either.map1 (elem(A)) (elem(B)))

  _,_ : Iset{ℓ₁} → Iset{ℓ₁} → Iset{ℓ₁}
  A , B = pair (singleton A) (pair A B)

  _⨯_ : Iset{ℓ₁} → Iset{ℓ₁} → Iset{ℓ₁}
  A ⨯ B = intro{Index = Index(A) Tuple.⨯ Index(B)} \{(ia Tuple., ib) → (elem(A)(ia) , elem(B)(ib))}

  ⋃ : Iset{ℓ₁} → Iset{ℓ₁}
  ⋃ A = intro{Index = Σ(Index(A)) (ia ↦ Index(elem(A)(ia)))} (\{(intro ia i) → elem(elem(A)(ia))(i)})

  filter : (A : Iset{ℓ₁}) → (Index(A) → Stmt{ℓ₁}) → Iset{ℓ₁}
  filter A P = intro {Index = Σ(Index(A)) P} (elem(A) ∘ Σ.left)

  {-
  filter2 : (A : Iset{Lvl.𝐒 ℓ₁}) → (Iset{ℓ₁} → Stmt{ℓ₁}) → Iset{Lvl.𝐒 ℓ₁}
  filter2 A P = intro {Index = Σ(Iset) P} (\{(intro i p) → {!i!}})
  -- intro i p
  -}

  filterBool : (A : Iset{ℓ₁}) → (Index(A) → Bool) → Iset{ℓ₁}
  filterBool A f = filter A (Lvl.Up ∘ IsTrue ∘ f)

  ℘ : Iset{ℓ₁} → Iset{ℓ₁}
  ℘ A = intro{Index = Index(A) → Bool} (filterBool A)
  -- intro{Index = Index(A) → Stmt} (filter A)
  -- TODO: How should one use Stmt and filter instead? The levels become a problem

  record _≡_ (A : Iset{ℓ₁}) (B : Iset{ℓ₁}) : Type{ℓ₁}
  record _⊆_ (A : Iset{ℓ₁}) (B : Iset{ℓ₁}) : Type{ℓ₁}
  _⊇_ : Iset{ℓ₁} → Iset{ℓ₁} → Type{ℓ₁}

  record _≡_ A B where
    coinductive
    constructor intro
    field
      left  : A ⊇ B
      right : A ⊆ B

  _∈_ : Iset{ℓ₁} → Iset{ℓ₁} → Type{ℓ₁}
  a ∈ B = ∃{Obj = Index(B)} (ib ↦ a ≡ elem(B)(ib))

  record _⊆_ A B where
    inductive
    constructor intro
    field
      map : Index(A) → Index(B)
      proof : ∀{ia} → (elem(A)(ia) ≡ elem(B)(map(ia)))

  A ⊇ B = B ⊆ A
  module _⊇_ where
    open _⊆_ public

  _∉_ : Iset{ℓ₁} → Iset{ℓ₁} → Type{ℓ₁}
  a ∉ B = ¬(a ∈ B)

  [≡]-to-[⊆] : ∀{A B : Iset{ℓ₁}} → (A ≡ B) → (A ⊆ B)
  [≡]-to-[⊆] = _≡_.right

  [≡]-to-[⊇] : ∀{A B : Iset{ℓ₁}} → (A ≡ B) → (A ⊇ B)
  [≡]-to-[⊇] = _≡_.left

  [≡]-reflexivity : ∀{A : Iset{ℓ₁}} → (A ≡ A)
  [⊆]-reflexivity : ∀{A : Iset{ℓ₁}} → (A ⊆ A)
  [⊇]-reflexivity : ∀{A : Iset{ℓ₁}} → (A ⊇ A)

  _≡_.left ([≡]-reflexivity {A = A}) = [⊇]-reflexivity {A = A}
  _≡_.right ([≡]-reflexivity {A = A}) = [⊆]-reflexivity {A = A}

  _⊆_.map    [⊆]-reflexivity = id
  _⊆_.proof ([⊆]-reflexivity {A = A}) {i} = [≡]-reflexivity {A = elem(A)(i)}

  [⊇]-reflexivity = [⊆]-reflexivity

  [≡]-symmetry : ∀{A B : Iset{ℓ₁}} → (A ≡ B) → (B ≡ A)
  _≡_.left  ([≡]-symmetry {A = A}{B = B} ab) = _≡_.right ab
  _≡_.right ([≡]-symmetry {A = A}{B = B} ab) = _≡_.left ab

  [≡]-transitivity : ∀{A B C : Iset{ℓ₁}} → (A ≡ B) → (B ≡ C) → (A ≡ C)
  [⊆]-transitivity : ∀{A B C : Iset{ℓ₁}} → (A ⊆ B) → (B ⊆ C) → (A ⊆ C)
  [⊇]-transitivity : ∀{A B C : Iset{ℓ₁}} → (A ⊇ B) → (B ⊇ C) → (A ⊇ C)

  _≡_.left  ([≡]-transitivity {A = A}{B = B}{C = C} ab bc) = [⊇]-transitivity {A = A}{B = B}{C = C} (_≡_.left ab) (_≡_.left bc)
  _≡_.right ([≡]-transitivity {A = A}{B = B}{C = C} ab bc) = [⊆]-transitivity {A = A}{B = B}{C = C} (_≡_.right ab) (_≡_.right bc)

  _⊆_.map   ([⊆]-transitivity {A = A} {B = B} {C = C} ab bc) = _⊆_.map bc ∘ _⊆_.map ab
  _⊆_.proof ([⊆]-transitivity {A = A} {B = B} {C = C} ab bc) {ia} = [≡]-transitivity {A = elem(A)(ia)}{B = elem B (_⊆_.map ab ia)} {C = elem(C)((_⊆_.map bc)((_⊆_.map ab)(ia)))} (_⊆_.proof ab {ia}) (_⊆_.proof bc)

  [⊇]-transitivity {A = A} {B = B} {C = C} ab bc = [⊆]-transitivity {A = C}{B = B}{C = A} bc ab

  [⊆]-antisymmetry : ∀{A B : Iset{ℓ₁}} → (A ⊇ B) → (A ⊆ B) → (A ≡ B)
  [⊆]-antisymmetry = intro

  [⊇]-antisymmetry : ∀{A B : Iset{ℓ₁}} → (A ⊆ B) → (A ⊇ B) → (A ≡ B)
  [⊇]-antisymmetry = swap intro

  [∈]-of-elem : ∀{A : Iset{ℓ₁}}{ia : Index(A)} → (elem(A)(ia) ∈ A)
  ∃.witness ([∈]-of-elem {ia = ia}) = ia
  ∃.proof    [∈]-of-elem = [≡]-reflexivity

  Iset-intro-self-equality : ∀{A : Iset{ℓ₁}} → (intro{Index = Index(A)}(elem(A)) ≡ A)
  _⊆_.map   (_≡_.left  Iset-intro-self-equality) = id
  _⊆_.map   (_≡_.right Iset-intro-self-equality) = id
  _⊆_.proof (_≡_.left  Iset-intro-self-equality) = [≡]-reflexivity
  _⊆_.proof (_≡_.right Iset-intro-self-equality) = [≡]-reflexivity

  [⊆]-with-elem : ∀{x y : Iset{ℓ₁}} → (xy : x ⊆ y) → ∀{ix} → (elem x ix ≡ elem y (_⊆_.map xy ix))
  [⊆]-with-elem (intro map proof) {ix} = proof{ix}

  [⊆]-inclusion : ∀{A : Iset{ℓ₁}}{B : Iset{ℓ₁}} → (∀{x : Iset{ℓ₁}} → (x ∈ A) → (x ∈ B)) ↔ (A ⊆ B)
  [⊆]-inclusion {A = A}{B = B} = [↔]-intro l r where
    l : (∀{x} → (x ∈ A) → (x ∈ B)) ← (A ⊆ B)
    ∃.witness (l (intro map proof) {x} xa) = map(∃.witness xa)
    ∃.proof   (l (intro map proof) {x} xa) = [≡]-transitivity (∃.proof xa) proof

    r : (∀{x} → (x ∈ A) → (x ∈ B)) → (A ⊆ B)
    _⊆_.map   (r proof) ia = [∃]-witness (proof{x = elem(A)(ia)} ([∈]-of-elem {A = A}))
    _⊆_.proof (r proof) {ia} = [∃]-proof (proof([∈]-of-elem {A = A}))

  [⊇]-inclusion : ∀{A : Iset{ℓ₁}}{B : Iset{ℓ₁}} → (∀{x : Iset{ℓ₁}} → (x ∈ A) ← (x ∈ B)) ↔ (A ⊇ B)
  [⊇]-inclusion {A = A}{B = B} = [⊆]-inclusion {A = B}{B = A}

  [≡]-inclusion : ∀{A : Iset{ℓ₁}}{B : Iset{ℓ₁}} → (∀{x : Iset{ℓ₁}} → (x ∈ A) ↔ (x ∈ B)) ↔ (A ≡ B)
  Tuple.left  (Tuple.left ([≡]-inclusion {A = A} {B = B}) ab) = [↔]-to-[←] [⊇]-inclusion (_≡_.left ab)
  Tuple.right (Tuple.left ([≡]-inclusion {A = A} {B = B}) ab) = [↔]-to-[←] [⊆]-inclusion (_≡_.right ab)
  _≡_.left  (Tuple.right ([≡]-inclusion {A = A} {B = B}) xaxb) = [↔]-to-[→] [⊇]-inclusion ([↔]-to-[←] xaxb)
  _≡_.right (Tuple.right ([≡]-inclusion {A = A} {B = B}) xaxb) = [↔]-to-[→] [⊆]-inclusion ([↔]-to-[→] xaxb)

  ∅-inclusion : ∀{x : Iset{ℓ₁}} → (x ∉ ∅)
  ∅-inclusion ()

  singleton-inclusion : ∀{a x : Iset{ℓ₁}} → (x ∈ singleton(a)) ↔ (x ≡ a)
  Tuple.left (singleton-inclusion {a = a} {x}) xin = [∃]-intro <> ⦃ xin ⦄
  Tuple.right (singleton-inclusion {a = a} {x}) ([∃]-intro i ⦃ eq ⦄ ) = eq

  [∪]-inclusion : ∀{A B x : Iset{ℓ₁}} → (x ∈ (A ∪ B)) ↔ (x ∈ A)∨(x ∈ B)
  Tuple.left ([∪]-inclusion {A = A} {B} {x}) ([∨]-introₗ ([∃]-intro ia)) = [∃]-intro (Either.Left  ia)
  Tuple.left ([∪]-inclusion {A = A} {B} {x}) ([∨]-introᵣ ([∃]-intro ib)) = [∃]-intro (Either.Right ib)
  Tuple.right ([∪]-inclusion {A = A} {B} {x}) ([∃]-intro ([∨]-introₗ ia)) = [∨]-introₗ ([∃]-intro ia)
  Tuple.right ([∪]-inclusion {A = A} {B} {x}) ([∃]-intro ([∨]-introᵣ ib)) = [∨]-introᵣ ([∃]-intro ib)

  [⋃]-inclusion : ∀{A x : Iset{ℓ₁}} → (x ∈ (⋃ A)) ↔ ∃(a ↦ (a ∈ A) ∧ (x ∈ a))
  Σ.left  (∃.witness (Tuple.left ([⋃]-inclusion {A = A} {x}) ([∃]-intro a ⦃ [∧]-intro ([∃]-intro iA) _ ⦄))) = iA
  Σ.right (∃.witness (Tuple.left ([⋃]-inclusion {A = A} {x}) ([∃]-intro a ⦃ [∧]-intro ([∃]-intro iA ⦃ aA ⦄) ([∃]-intro ia) ⦄))) = _⊆_.map (_≡_.right aA) ia
  ∃.proof (Tuple.left ([⋃]-inclusion {A = A} {x}) ([∃]-intro a ⦃ [∧]-intro ([∃]-intro iA ⦃ aA ⦄) ([∃]-intro ia ⦃ xa ⦄) ⦄)) = [≡]-transitivity xa ([⊆]-with-elem ([≡]-to-[⊆] aA) {ia})
  ∃.witness (Tuple.right ([⋃]-inclusion {A = A} {x}) ([∃]-intro (intro iA ia) ⦃ proof ⦄)) = elem(A)(iA)
  Tuple.left (∃.proof (Tuple.right ([⋃]-inclusion {A = A} {x}) ([∃]-intro (intro iA ia) ⦃ proof ⦄))) = [∈]-of-elem {A = A}
  ∃.witness (Tuple.right (∃.proof (Tuple.right ([⋃]-inclusion {A = A} {x}) ([∃]-intro (intro iA ia) ⦃ proof ⦄)))) = ia
  ∃.proof (Tuple.right (∃.proof (Tuple.right ([⋃]-inclusion {A = A} {x}) ([∃]-intro (intro iA ia) ⦃ proof ⦄)))) = proof

  {-
  filter-inclusion : ∀{A : Iset{ℓ₁}}{i : Index(A)}{P} → (elem(A)(i) ∈ filter A P) ↔ P(i)
  Σ.left             (∃.witness (Tuple.left (filter-inclusion {i = i}) pi)) = i
  Σ.right            (∃.witness (Tuple.left (filter-inclusion {i = i}) pi)) = pi
  _≡_.left  (∃.proof (Tuple.left filter-inclusion pi)) = intro id [≡]-reflexivity
  _≡_.right (∃.proof (Tuple.left filter-inclusion pi)) = intro id [≡]-reflexivity
  Tuple.right (filter-inclusion {i = i}) ([∃]-intro (intro iA PiA) ⦃ [≡]-intro ⦄) = {!!}
  -- {!_⊇_.proof ([≡]-to-[⊇] proof) {intro ? ?}!}
  -}

  -- Iset-induction : ∀{P : Iset{ℓ₁} → Stmt{ℓ₂}} → (∀{I : Type{ℓ₁}}{e : I → Iset{ℓ₁}} → ((∀{i : I} → P(e(i))) → P(Iset.intro(e)))) → (∀{A : Iset{ℓ₁}} → P(A))
  -- Iset-induction {P = P} proof {A} = proof {Index(A)} {elem(A)} ?

  --Iset-induction : ∀{P : Iset{ℓ₁} → Stmt{ℓ₂}} → (∀{A : Iset{ℓ₁}} → (∀{i : Index(A)} → P(elem(A)(i))) → P(A)) → (∀{A : Iset{ℓ₁}} → P(A))
  -- Iset-induction {ℓ₁} {ℓ₂} {P} proof {A} = proof{A} \{i} → Iset-induction{P = P} proof {elem(A)(i)}

  -- Iset-2-2 : ∀{P : Iset{ℓ₁} → Stmt{ℓ₂}} → (∀{x : Iset{ℓ₁}} → (∀{y : Iset{ℓ₁}} → (y ∈ x) → P(y) → P(x))) → (∀{A : Iset{ℓ₁}} → P(A))
  -- Iset-2-2 {P = P} proof {A = A} = Iset-induction {P = P} {Index(A)}{elem(A)} (p ↦ proof {intro (elem(A))}{A} {!!} {!!}) {A = A}
