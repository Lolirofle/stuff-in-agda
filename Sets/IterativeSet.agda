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
open import Sets.Setoid using (Equiv ; UnaryRelator ; BinaryRelator ; intro)
open import Structure.Function.Domain
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Syntax.Function
open import Type
open import Type.Dependent

module _ where
  private variable {ℓ ℓ₁ ℓ₂} : Lvl.Level

  -- A model of constructive set theory (CZF) using iterative sets through W-types.
  -- TODO: Is it really? How are power sets handled?
  record Iset : Type{Lvl.𝐒(ℓ)} where
    inductive
    constructor intro
    field
      {Index} : Type{ℓ}
      elem : Index → Iset{ℓ}
  open Iset

  ∅ : Iset{ℓ}
  ∅ = intro{Index = Empty} empty

  singleton : Iset{ℓ} → Iset{ℓ}
  singleton = intro{Index = Unit} ∘ const

  pair : Iset{ℓ} → Iset{ℓ} → Iset{ℓ}
  pair A B = intro{Index = Lvl.Up(Bool)} \{(Lvl.up 𝐹) → A ; (Lvl.up 𝑇) → B}

  _∪_ : Iset{ℓ} → Iset{ℓ} → Iset{ℓ}
  A ∪ B = intro{Index = Index(A) ‖ Index(B)} (Either.map1 (elem(A)) (elem(B)))

  _,_ : Iset{ℓ} → Iset{ℓ} → Iset{ℓ}
  A , B = pair (singleton A) (pair A B)

  _⨯_ : Iset{ℓ} → Iset{ℓ} → Iset{ℓ}
  A ⨯ B = intro{Index = Index(A) Tuple.⨯ Index(B)} \{(ia Tuple., ib) → (elem(A)(ia) , elem(B)(ib))}

  ⋃ : Iset{ℓ} → Iset{ℓ}
  ⋃ A = intro{Index = Σ(Index(A)) (ia ↦ Index(elem(A)(ia)))} (\{(intro ia i) → elem(elem(A)(ia))(i)})

  indexFilter : (A : Iset{ℓ}) → (Index(A) → Stmt{ℓ}) → Iset{ℓ}
  indexFilter A P = intro {Index = Σ(Index(A)) P} (elem(A) ∘ Σ.left)

  filter : (A : Iset{ℓ}) → (Iset{ℓ} → Stmt{ℓ}) → Iset{ℓ}
  filter{ℓ} A P = indexFilter A (P ∘ elem(A))

  indexFilterBool : (A : Iset{ℓ}) → (Index(A) → Bool) → Iset{ℓ}
  indexFilterBool A f = indexFilter A (Lvl.Up ∘ IsTrue ∘ f)

  filterBool : (A : Iset{ℓ}) → (Iset{ℓ} → Bool) → Iset{ℓ}
  filterBool A f = indexFilterBool A (f ∘ elem(A))

  -- ℘ : Iset{Lvl.𝐒 ℓ} → Iset{Lvl.𝐒 ℓ}
  -- ℘ A = intro{Index = Index(A) → Bool} (indexFilterBool A)
  -- ℘{ℓ} A = intro{Lvl.𝐒 ℓ}{Index = Index(A) → Stmt{Lvl.𝟎}} {!indexFilter(A)!}
  -- TODO: How should one use Stmt and filter instead? The levels become a problem

  record _≡_ (A : Iset{ℓ}) (B : Iset{ℓ}) : Type{ℓ}
  record _⊆_ (A : Iset{ℓ}) (B : Iset{ℓ}) : Type{ℓ}
  _⊇_ : Iset{ℓ} → Iset{ℓ} → Type{ℓ}

  record _≡_ A B where
    coinductive
    constructor intro
    field
      left  : A ⊇ B
      right : A ⊆ B

  _∈_ : Iset{ℓ} → Iset{ℓ} → Type{ℓ}
  a ∈ B = ∃{Obj = Index(B)} (ib ↦ a ≡ elem(B)(ib))

  record _⊆_ A B where
    inductive
    constructor intro
    field
      map : Index(A) → Index(B)
      proof : ∀{ia} → (elem(A)(ia) ≡ elem(B)(map(ia))) -- TODO: If Index is a setoid, then I think this should be changed to ∀{ia ib} → (ia ≡ ib) → (elem(A)(ia) ≡ elem(B)(map(ib)))

  A ⊇ B = B ⊆ A
  module _⊇_ where
    open _⊆_ public

  _∉_ : Iset{ℓ} → Iset{ℓ} → Type{ℓ}
  a ∉ B = ¬(a ∈ B)

  instance
    [≡][⊆]-sub : (_≡_) ⊆₂ (_⊆_ {ℓ})
    [≡][⊆]-sub = intro _≡_.right

  instance
    [≡][⊇]-sub : (_≡_) ⊆₂ (_⊇_ {ℓ})
    [≡][⊇]-sub = intro _≡_.left

  [≡]-reflexivity-raw : ∀{A : Iset{ℓ}} → (A ≡ A)
  [⊆]-reflexivity-raw : ∀{A : Iset{ℓ}} → (A ⊆ A)
  [⊇]-reflexivity-raw : ∀{A : Iset{ℓ}} → (A ⊇ A)

  _≡_.left ([≡]-reflexivity-raw {A = A}) = [⊇]-reflexivity-raw {A = A}
  _≡_.right ([≡]-reflexivity-raw {A = A}) = [⊆]-reflexivity-raw {A = A}

  _⊆_.map    [⊆]-reflexivity-raw = id
  _⊆_.proof ([⊆]-reflexivity-raw {A = A}) {i} = [≡]-reflexivity-raw {A = elem(A)(i)}

  [⊇]-reflexivity-raw = [⊆]-reflexivity-raw

  [≡]-symmetry-raw : ∀{A B : Iset{ℓ}} → (A ≡ B) → (B ≡ A)
  _≡_.left  ([≡]-symmetry-raw {A = A}{B = B} ab) = _≡_.right ab
  _≡_.right ([≡]-symmetry-raw {A = A}{B = B} ab) = _≡_.left ab

  [≡]-transitivity-raw : ∀{A B C : Iset{ℓ}} → (A ≡ B) → (B ≡ C) → (A ≡ C)
  [⊆]-transitivity-raw : ∀{A B C : Iset{ℓ}} → (A ⊆ B) → (B ⊆ C) → (A ⊆ C)
  [⊇]-transitivity-raw : ∀{A B C : Iset{ℓ}} → (A ⊇ B) → (B ⊇ C) → (A ⊇ C)

  _≡_.left  ([≡]-transitivity-raw {A = A}{B = B}{C = C} ab bc) = [⊇]-transitivity-raw {A = A}{B = B}{C = C} (_≡_.left ab) (_≡_.left bc)
  _≡_.right ([≡]-transitivity-raw {A = A}{B = B}{C = C} ab bc) = [⊆]-transitivity-raw {A = A}{B = B}{C = C} (_≡_.right ab) (_≡_.right bc)

  _⊆_.map   ([⊆]-transitivity-raw {A = A} {B = B} {C = C} ab bc) = _⊆_.map bc ∘ _⊆_.map ab
  _⊆_.proof ([⊆]-transitivity-raw {A = A} {B = B} {C = C} ab bc) {ia} = [≡]-transitivity-raw {A = elem(A)(ia)}{B = elem B (_⊆_.map ab ia)} {C = elem(C)((_⊆_.map bc)((_⊆_.map ab)(ia)))} (_⊆_.proof ab {ia}) (_⊆_.proof bc)

  [⊇]-transitivity-raw {A = A} {B = B} {C = C} ab bc = [⊆]-transitivity-raw {A = C}{B = B}{C = A} bc ab



  instance
    [≡]-reflexivity : Reflexivity(_≡_ {ℓ})
    [≡]-reflexivity = intro [≡]-reflexivity-raw
  instance
    [⊆]-reflexivity : Reflexivity(_⊆_ {ℓ})
    [⊆]-reflexivity = intro [⊆]-reflexivity-raw
  instance
    [⊇]-reflexivity : Reflexivity(_⊇_ {ℓ})
    [⊇]-reflexivity = intro [⊇]-reflexivity-raw
  instance
    [≡]-symmetry : Symmetry(_≡_ {ℓ})
    [≡]-symmetry = intro [≡]-symmetry-raw
  instance
    [⊆]-antisymmetry : Antisymmetry(_⊆_ {ℓ})(_≡_)
    [⊆]-antisymmetry = intro (swap intro)
  instance
    [⊇]-antisymmetry : Antisymmetry(_⊇_ {ℓ})(_≡_)
    [⊇]-antisymmetry = intro intro
  instance
    [≡]-transitivity : Transitivity(_≡_ {ℓ})
    [≡]-transitivity = intro [≡]-transitivity-raw
  instance
    [⊆]-transitivity : Transitivity(_⊆_ {ℓ})
    [⊆]-transitivity = intro [⊆]-transitivity-raw
  instance
    [⊇]-transitivity : Transitivity(_⊇_ {ℓ})
    [⊇]-transitivity = intro [⊇]-transitivity-raw
  instance
    [≡]-equivalence : Equivalence(_≡_ {ℓ})
    [≡]-equivalence = intro
  {- TODO: Iset equivalence and Isets are not on the same level
  instance
    Iset-equiv : Equiv(Iset{ℓ})
    Iset-equiv = {!intro(_≡_)!}
  -}


  Iset-induction : ∀{P : Iset{ℓ₁} → Stmt{ℓ₂}} → (∀{A : Iset{ℓ₁}} → (∀{i : Index(A)} → P(elem(A)(i))) → P(A)) → (∀{A : Iset{ℓ₁}} → P(A))
  Iset-induction {P = P} proof {intro Aelem} = proof{_} \{i} → Iset-induction{P = P} proof {Aelem(i)}

  [∈]-of-elem : ∀{A : Iset{ℓ}}{ia : Index(A)} → (elem(A)(ia) ∈ A)
  ∃.witness ([∈]-of-elem {ia = ia}) = ia
  ∃.proof    [∈]-of-elem = [≡]-reflexivity-raw

  Iset-intro-self-equality : ∀{A : Iset{ℓ}} → (intro{Index = Index(A)}(elem(A)) ≡ A)
  _⊆_.map   (_≡_.left  Iset-intro-self-equality) = id
  _⊆_.map   (_≡_.right Iset-intro-self-equality) = id
  _⊆_.proof (_≡_.left  Iset-intro-self-equality) = [≡]-reflexivity-raw
  _⊆_.proof (_≡_.right Iset-intro-self-equality) = [≡]-reflexivity-raw

  [⊆]-with-elem : ∀{x y : Iset{ℓ}} → (xy : x ⊆ y) → ∀{ix} → (elem x ix ≡ elem y (_⊆_.map xy ix))
  [⊆]-with-elem (intro map proof) {ix} = proof{ix}

  -- TODO: When is this true
  -- elemᵣ-injectivity : ∀{x : Iset{ℓ}} → ∀{i₁ i₂} → (elem x i₁ ≡ elem x i₂) → (i₁ ≡ i₂)
  -- elemᵣ-injectivity x = {!!}



  [⊆]-inclusion : ∀{A : Iset{ℓ}}{B : Iset{ℓ}} → (∀{x : Iset{ℓ}} → (x ∈ A) → (x ∈ B)) ↔ (A ⊆ B)
  [⊆]-inclusion {A = A}{B = B} = [↔]-intro l r where
    l : (∀{x} → (x ∈ A) → (x ∈ B)) ← (A ⊆ B)
    ∃.witness (l (intro map proof) {x} xa) = map(∃.witness xa)
    ∃.proof   (l (intro map proof) {x} xa) = [≡]-transitivity-raw (∃.proof xa) proof

    r : (∀{x} → (x ∈ A) → (x ∈ B)) → (A ⊆ B)
    _⊆_.map   (r proof) ia = [∃]-witness (proof{x = elem(A)(ia)} ([∈]-of-elem {A = A}))
    _⊆_.proof (r proof) {ia} = [∃]-proof (proof([∈]-of-elem {A = A}))

  [⊇]-inclusion : ∀{A : Iset{ℓ}}{B : Iset{ℓ}} → (∀{x : Iset{ℓ}} → (x ∈ A) ← (x ∈ B)) ↔ (A ⊇ B)
  [⊇]-inclusion {A = A}{B = B} = [⊆]-inclusion {A = B}{B = A}

  [≡]-inclusion : ∀{A : Iset{ℓ}}{B : Iset{ℓ}} → (∀{x : Iset{ℓ}} → (x ∈ A) ↔ (x ∈ B)) ↔ (A ≡ B)
  Tuple.left  (Tuple.left ([≡]-inclusion {A = A} {B = B}) ab) = [↔]-to-[←] [⊇]-inclusion (_≡_.left ab)
  Tuple.right (Tuple.left ([≡]-inclusion {A = A} {B = B}) ab) = [↔]-to-[←] [⊆]-inclusion (_≡_.right ab)
  _≡_.left  (Tuple.right ([≡]-inclusion {A = A} {B = B}) xaxb) = [↔]-to-[→] [⊇]-inclusion ([↔]-to-[←] xaxb)
  _≡_.right (Tuple.right ([≡]-inclusion {A = A} {B = B}) xaxb) = [↔]-to-[→] [⊆]-inclusion ([↔]-to-[→] xaxb)



  -- [∈]ₗ-unaryRelation : ∀{B} → UnaryRelator(_∈ B)
  -- [∈]ₗ-unaryRelation = {!!}
  [∈]ₗ-unaryRelation-raw : ∀{A₁ A₂ B : Iset{ℓ}} → (A₁ ≡ A₂) → (A₁ ∈ B) → (A₂ ∈ B)
  ∃.witness ([∈]ₗ-unaryRelation-raw pa ([∃]-intro i ⦃ p ⦄)) = i
  ∃.proof ([∈]ₗ-unaryRelation-raw pa ([∃]-intro i ⦃ p ⦄)) = [≡]-transitivity-raw ([≡]-symmetry-raw pa) p

  [∈]-binaryRelation-raw : ∀{A₁ A₂ B₁ B₂ : Iset{ℓ}} → (A₁ ≡ A₂) → (B₁ ≡ B₂) → ((A₁ ∈ B₁) → (A₂ ∈ B₂))
  [∈]-binaryRelation-raw {B₂ = B₂} pa pb = [∈]ₗ-unaryRelation-raw {B = B₂} pa ∘ [↔]-to-[←] [⊆]-inclusion (sub₂(_≡_)(_⊆_) pb)



  ∅-inclusion : ∀{x : Iset{ℓ}} → (x ∉ ∅)
  ∅-inclusion ()

  singleton-inclusion : ∀{a x : Iset{ℓ}} → (x ∈ singleton(a)) ↔ (x ≡ a)
  Tuple.left (singleton-inclusion {a = a} {x}) xin = [∃]-intro <> ⦃ xin ⦄
  Tuple.right (singleton-inclusion {a = a} {x}) ([∃]-intro i ⦃ eq ⦄ ) = eq

  [∪]-inclusion : ∀{A B x : Iset{ℓ}} → (x ∈ (A ∪ B)) ↔ (x ∈ A)∨(x ∈ B)
  Tuple.left ([∪]-inclusion {A = A} {B} {x}) ([∨]-introₗ ([∃]-intro ia)) = [∃]-intro (Either.Left  ia)
  Tuple.left ([∪]-inclusion {A = A} {B} {x}) ([∨]-introᵣ ([∃]-intro ib)) = [∃]-intro (Either.Right ib)
  Tuple.right ([∪]-inclusion {A = A} {B} {x}) ([∃]-intro ([∨]-introₗ ia)) = [∨]-introₗ ([∃]-intro ia)
  Tuple.right ([∪]-inclusion {A = A} {B} {x}) ([∃]-intro ([∨]-introᵣ ib)) = [∨]-introᵣ ([∃]-intro ib)

  [⋃]-inclusion : ∀{A x : Iset{ℓ}} → (x ∈ (⋃ A)) ↔ ∃(a ↦ (a ∈ A) ∧ (x ∈ a))
  Σ.left  (∃.witness (Tuple.left ([⋃]-inclusion {A = A} {x}) ([∃]-intro a ⦃ [∧]-intro ([∃]-intro iA) _ ⦄))) = iA
  Σ.right (∃.witness (Tuple.left ([⋃]-inclusion {A = A} {x}) ([∃]-intro a ⦃ [∧]-intro ([∃]-intro iA ⦃ aA ⦄) ([∃]-intro ia) ⦄))) = _⊆_.map (_≡_.right aA) ia
  ∃.proof (Tuple.left ([⋃]-inclusion {A = A} {x}) ([∃]-intro a ⦃ [∧]-intro ([∃]-intro iA ⦃ aA ⦄) ([∃]-intro ia ⦃ xa ⦄) ⦄)) = [≡]-transitivity-raw xa ([⊆]-with-elem (sub₂(_≡_)(_⊆_) aA) {ia})
  ∃.witness (Tuple.right ([⋃]-inclusion {A = A} {x}) ([∃]-intro (intro iA ia) ⦃ proof ⦄)) = elem(A)(iA)
  Tuple.left (∃.proof (Tuple.right ([⋃]-inclusion {A = A} {x}) ([∃]-intro (intro iA ia) ⦃ proof ⦄))) = [∈]-of-elem {A = A}
  ∃.witness (Tuple.right (∃.proof (Tuple.right ([⋃]-inclusion {A = A} {x}) ([∃]-intro (intro iA ia) ⦃ proof ⦄)))) = ia
  ∃.proof (Tuple.right (∃.proof (Tuple.right ([⋃]-inclusion {A = A} {x}) ([∃]-intro (intro iA ia) ⦃ proof ⦄)))) = proof

  -- TODO: This should be true when result is an Iset? Because that is why filter-inclusion works?
  -- test-injective : ∀{A : Iset{ℓ}} → Injective(elem(A))

  {-UnaryRelator : (Iset{ℓ₁} → Stmt{ℓ₂}) → Stmt
  UnaryRelator(P) = ∀{x y} → (x ≡ y) → (P(x) → P(y))

  filter-inclusionᵣ : ∀{A : Iset{ℓ}}{i : Index(A)}{P} → UnaryRelator(P) → (elem(A)(i) ∈ filter A P) → P(elem(A)(i))
  filter-inclusionᵣ {i = i} subst ([∃]-intro (intro iA PiA) ⦃ pp ⦄) = subst ([≡]-symmetry-raw pp) PiA-}

  {-
  -- TODO: Assume setoid on Index(A), UnaryRelator(P), and injectivity on (elem A) for this proof to work
  indexFilter-inclusion : ∀{A : Iset{ℓ}}{i : Index(A)}{P} → (elem(A)(i) ∈ indexFilter A P) ↔ P(i)
  Σ.left             (∃.witness (Tuple.left (indexFilter-inclusion {i = i}) pi)) = i
  Σ.right            (∃.witness (Tuple.left (indexFilter-inclusion {i = i}) pi)) = pi
  _≡_.left  (∃.proof (Tuple.left indexFilter-inclusion pi)) = intro id [≡]-reflexivity-raw
  _≡_.right (∃.proof (Tuple.left indexFilter-inclusion pi)) = intro id [≡]-reflexivity-raw
  Tuple.right (indexFilter-inclusion {i = i} {P = P}) ([∃]-intro (intro iA PiA) ⦃ pp ⦄) = {!!}
  -}

  -- Iset-2-2 : ∀{P : Iset{ℓ} → Stmt{ℓ₂}} → (∀{x : Iset{ℓ}} → (∀{y : Iset{ℓ}} → (y ∈ x) → P(y) → P(x))) → (∀{A : Iset{ℓ}} → P(A))
  -- Iset-2-2 {P = P} proof {A = A} = Iset-induction {P = P} {Index(A)}{elem(A)} (p ↦ proof {intro (elem(A))}{A} {!!} {!!}) {A = A}
