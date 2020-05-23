{-# OPTIONS --guardedness #-}

module Sets.IterativeSet where

import      Lvl
open import Data
open import Data.Boolean
open import Data.Boolean.Proofs
open import Data.Boolean.Stmt
open import Data.Boolean.Stmt.Proofs
open import Data.Either as Either using (_‖_)
open import Data.Tuple as Tuple using ()
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural
open import Relator.Equals using () renaming (_≡_ to Id ; [≡]-intro to intro)
open import Structure.Setoid.WithLvl using (Equiv)
open import Structure.Function.Domain
open import Structure.Function
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Relator
open import Syntax.Function
open import Syntax.Transitivity
open import Type
open import Type.Dependent

module _ where
  private variable {ℓ ℓ₁ ℓ₂} : Lvl.Level

  -- A model of constructive set theory (CZF) by iterative sets through W-types.
  record Iset : Type{Lvl.𝐒(ℓ)} where
    inductive
    pattern
    constructor intro
    field
      {Index} : Type{ℓ}
      elem : Index → Iset{ℓ}
  open Iset

  -- The empty set, consisting of no elements.
  -- Index is the empty type, which means that there are no objects pointing to elements in the set.
  ∅ : Iset{ℓ}
  ∅ = intro{Index = Empty} empty

  -- The singleton set, consisting of one element.
  -- Index is the unit type, which means that there are a single object pointing to a single element in the set.
  singleton : Iset{ℓ} → Iset{ℓ}
  singleton = intro{Index = Unit} ∘ const

  -- The pair set, consisting of two elements.
  -- Index is the boolean type, which means that there are two objects pointing to two elements in the set.
  pair : Iset{ℓ} → Iset{ℓ} → Iset{ℓ}
  pair A B = intro{Index = Lvl.Up(Bool)} \{(Lvl.up 𝐹) → A ; (Lvl.up 𝑇) → B}

  -- The union operator.
  -- Index(A ∪ B) is the either type of two indices, which means that both objects from the A and the B index point to elements in the set.
  _∪_ : Iset{ℓ} → Iset{ℓ} → Iset{ℓ}
  A ∪ B = intro{Index = Index(A) ‖ Index(B)} (Either.map1 (elem(A)) (elem(B)))

  _,_ : Iset{ℓ} → Iset{ℓ} → Iset{ℓ}
  A , B = pair (singleton A) (pair A B)

  _⨯_ : Iset{ℓ} → Iset{ℓ} → Iset{ℓ}
  A ⨯ B = intro{Index = Index(A) Tuple.⨯ Index(B)} \{(ia Tuple., ib) → (elem(A)(ia) , elem(B)(ib))}

  -- The big union operator.
  -- Index(⋃ A) is the dependent sum type of an Index(A) and the index of the element this index points to.
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

  mapSet : (Iset{ℓ} → Iset{ℓ}) → (Iset{ℓ} → Iset{ℓ})
  mapSet f(A) = intro{Index = Index(A)} (f ∘ elem(A))

  -- The power set operator.
  -- Index(℘(A)) is a function type. An instance of such a function represents a subset, and essentially maps every element in A to a boolean which is interpreted as "in the subset of not".
  -- Note: This only works properly in a classical setting. Trying to use indexFilter instead result in universe level problems.
  ℘ : Iset{ℓ} → Iset{ℓ}
  ℘(A) = intro{Index = Index(A) → Bool} (indexFilterBool A)

  -- The set of ordinal numbers of the first order.
  ω : Iset{ℓ}
  ω = intro{Index = Lvl.Up ℕ} (N ∘ Lvl.Up.obj) where
    N : ℕ → Iset{ℓ}
    N(𝟎)    = ∅
    N(𝐒(n)) = N(n) ∪ singleton(N(n))

  record _≡_ (A : Iset{ℓ₁}) (B : Iset{ℓ₂}) : Type{ℓ₁ Lvl.⊔ ℓ₂}
  record _⊆_ (A : Iset{ℓ₁}) (B : Iset{ℓ₂}) : Type{ℓ₁ Lvl.⊔ ℓ₂}
  _⊇_ : Iset{ℓ₁} → Iset{ℓ₂} → Type{ℓ₁ Lvl.⊔ ℓ₂}

  -- Set equality is by definition the antisymmetric property of the subset relation.
  record _≡_ A B where
    coinductive
    constructor intro
    field
      left  : A ⊇ B
      right : A ⊆ B

  -- Set membership is the existence of an index in the set that points to a set equal element to the element.
  _∈_ : Iset{ℓ₁} → Iset{ℓ₂} → Type{ℓ₁ Lvl.⊔ ℓ₂}
  a ∈ B = ∃{Obj = Index(B)} (ib ↦ a ≡ elem(B)(ib))

  -- Set subset is a mapping between the indices such that they point to the same element in both sets.
  record _⊆_ A B where
    inductive
    constructor intro
    field
      map : Index(A) → Index(B)
      proof : ∀{ia} → (elem(A)(ia) ≡ elem(B)(map(ia))) -- TODO: If Index is a setoid, then I think this should be changed to ∀{ia ib} → (ia ≡ ib) → (elem(A)(ia) ≡ elem(B)(map(ib)))

  A ⊇ B = B ⊆ A
  module _⊇_ where
    open _⊆_ public

  _∉_ : Iset{ℓ₁} → Iset{ℓ₂} → Type{ℓ₁ Lvl.⊔ ℓ₂}
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
  instance
    Iset-equiv : Equiv(Iset{ℓ})
    Equiv._≡_ Iset-equiv = _≡_
    Equiv.equivalence Iset-equiv = [≡]-equivalence



  Iset-index-induction : ∀{P : Iset{ℓ₁} → Stmt{ℓ₂}} → (∀{A : Iset{ℓ₁}} → (∀{i : Index(A)} → P(elem(A)(i))) → P(A)) → (∀{A : Iset{ℓ₁}} → P(A))
  Iset-index-induction {P = P} proof {intro elem} = proof{_} \{i} → Iset-index-induction{P = P} proof {elem(i)}

  Iset-induction : ∀{P : Iset{ℓ₁} → Stmt{ℓ₂}} ⦃ _ : UnaryRelator(P) ⦄ → (∀{A : Iset{ℓ₁}} → (∀{a} → (a ∈ A) → P(a)) → P(A)) → (∀{A : Iset{ℓ₁}} → P(A))
  Iset-induction {P = P} p = Iset-index-induction (\{A} pp → p{A} (\{a} aA → substitute₁(P) (symmetry(_≡_) ([∃]-proof aA)) (pp{[∃]-witness aA})))

  [∈]-of-elem : ∀{A : Iset{ℓ}}{ia : Index(A)} → (elem(A)(ia) ∈ A)
  ∃.witness ([∈]-of-elem {ia = ia}) = ia
  ∃.proof    [∈]-of-elem = [≡]-reflexivity-raw

  Iset-intro-self-equality : ∀{A : Iset{ℓ}} → (intro{Index = Index(A)}(elem(A)) ≡ A)
  _⊆_.map   (_≡_.left  Iset-intro-self-equality) = id
  _⊆_.map   (_≡_.right Iset-intro-self-equality) = id
  _⊆_.proof (_≡_.left  Iset-intro-self-equality) = [≡]-reflexivity-raw
  _⊆_.proof (_≡_.right Iset-intro-self-equality) = [≡]-reflexivity-raw

  [⊆]-with-elem : ∀{x y : Iset{ℓ}} → (xy : x ⊆ y) → ∀{ix} → (elem x ix ≡ elem y (_⊆_.map xy ix))
  [⊆]-with-elem xy {ix} = _⊆_.proof xy {ix}



  [⊆]-membership : ∀{A : Iset{ℓ}}{B : Iset{ℓ}} → (∀{x : Iset{ℓ}} → (x ∈ A) → (x ∈ B)) ↔ (A ⊆ B)
  [⊆]-membership {A = A}{B = B} = [↔]-intro l r where
    l : (∀{x} → (x ∈ A) → (x ∈ B)) ← (A ⊆ B)
    ∃.witness (l AB {x} xa) = _⊆_.map AB (∃.witness xa)
    ∃.proof   (l AB {x} xa) = [≡]-transitivity-raw (∃.proof xa) (_⊆_.proof AB)

    r : (∀{x} → (x ∈ A) → (x ∈ B)) → (A ⊆ B)
    _⊆_.map   (r proof) ia = [∃]-witness (proof{x = elem(A)(ia)} ([∈]-of-elem {A = A}))
    _⊆_.proof (r proof) {ia} = [∃]-proof (proof([∈]-of-elem {A = A}))

  [⊇]-membership : ∀{A : Iset{ℓ}}{B : Iset{ℓ}} → (∀{x : Iset{ℓ}} → (x ∈ A) ← (x ∈ B)) ↔ (A ⊇ B)
  [⊇]-membership {A = A}{B = B} = [⊆]-membership {A = B}{B = A}

  [≡]-membership : ∀{A : Iset{ℓ}}{B : Iset{ℓ}} → (∀{x : Iset{ℓ}} → (x ∈ A) ↔ (x ∈ B)) ↔ (A ≡ B)
  Tuple.left  (Tuple.left ([≡]-membership {A = A} {B = B}) ab) = [↔]-to-[←] [⊇]-membership (_≡_.left ab)
  Tuple.right (Tuple.left ([≡]-membership {A = A} {B = B}) ab) = [↔]-to-[←] [⊆]-membership (_≡_.right ab)
  _≡_.left  (Tuple.right ([≡]-membership {A = A} {B = B}) xaxb) = [↔]-to-[→] [⊇]-membership ([↔]-to-[←] xaxb)
  _≡_.right (Tuple.right ([≡]-membership {A = A} {B = B}) xaxb) = [↔]-to-[→] [⊆]-membership ([↔]-to-[→] xaxb)



  [∈]ₗ-unaryRelation-raw : ∀{A₁ A₂ B : Iset{ℓ}} → (A₁ ≡ A₂) → (A₁ ∈ B) → (A₂ ∈ B)
  ∃.witness ([∈]ₗ-unaryRelation-raw pa ([∃]-intro i ⦃ p ⦄)) = i
  ∃.proof ([∈]ₗ-unaryRelation-raw pa ([∃]-intro i ⦃ p ⦄)) = [≡]-transitivity-raw ([≡]-symmetry-raw pa) p

  [∈]-binaryRelation-raw : ∀{A₁ A₂ B₁ B₂ : Iset{ℓ}} → (A₁ ≡ A₂) → (B₁ ≡ B₂) → ((A₁ ∈ B₁) → (A₂ ∈ B₂))
  [∈]-binaryRelation-raw {B₂ = B₂} pa pb = [∈]ₗ-unaryRelation-raw {B = B₂} pa ∘ [↔]-to-[←] [⊆]-membership (sub₂(_≡_)(_⊆_) pb)

  instance
    [∈]-binaryRelation : BinaryRelator(_∈_ {ℓ})
    [∈]-binaryRelation = intro [∈]-binaryRelation-raw

  instance
    [⊆]-binaryRelator : BinaryRelator(_⊆_ {ℓ}{ℓ})
    BinaryRelator.substitution [⊆]-binaryRelator p1 p2 ps = sub₂(_≡_)(_⊇_) p1 🝖 ps 🝖 sub₂(_≡_)(_⊆_) p2



  -- If there is an element in the empty set, then there exists an instance of the empty type by definition, and that is false by definition.
  ∅-membership : ∀{x : Iset{ℓ₁}} → (x ∉ ∅ {ℓ₂})
  ∅-membership ()

  -- There is a bijection between (A ‖ B) and ∃{Lvl.Up Bool}(\{(Lvl.up 𝐹) → A ; (Lvl.up 𝑇) → B}).
  pair-membership : ∀{a b x : Iset{ℓ}} → (x ∈ pair a b) ↔ (x ≡ a)∨(x ≡ b)
  Tuple.left (pair-membership {a = a} {x}) ([∨]-introₗ p) = [∃]-intro (Lvl.up 𝐹) ⦃ p ⦄
  Tuple.left (pair-membership {a = a} {x}) ([∨]-introᵣ p) = [∃]-intro (Lvl.up 𝑇) ⦃ p ⦄
  Tuple.right (pair-membership {a = a} {x}) ([∃]-intro (Lvl.up 𝐹) ⦃ eq ⦄) = [∨]-introₗ eq
  Tuple.right (pair-membership {a = a} {x}) ([∃]-intro (Lvl.up 𝑇) ⦃ eq ⦄) = [∨]-introᵣ eq

  -- There is a bijection between (A) and ∃{Unit}(\{<> → A}).
  singleton-membership : ∀{a x : Iset{ℓ}} → (x ∈ singleton(a)) ↔ (x ≡ a)
  Tuple.left (singleton-membership {a = a} {x}) xin = [∃]-intro <> ⦃ xin ⦄
  Tuple.right (singleton-membership {a = a} {x}) ([∃]-intro i ⦃ eq ⦄ ) = eq

  [∪]-membership : ∀{A B x : Iset{ℓ}} → (x ∈ (A ∪ B)) ↔ (x ∈ A)∨(x ∈ B)
  Tuple.left ([∪]-membership {A = A} {B} {x}) ([∨]-introₗ ([∃]-intro ia)) = [∃]-intro (Either.Left  ia)
  Tuple.left ([∪]-membership {A = A} {B} {x}) ([∨]-introᵣ ([∃]-intro ib)) = [∃]-intro (Either.Right ib)
  Tuple.right ([∪]-membership {A = A} {B} {x}) ([∃]-intro ([∨]-introₗ ia)) = [∨]-introₗ ([∃]-intro ia)
  Tuple.right ([∪]-membership {A = A} {B} {x}) ([∃]-intro ([∨]-introᵣ ib)) = [∨]-introᵣ ([∃]-intro ib)

  [⋃]-membership : ∀{A x : Iset{ℓ}} → (x ∈ (⋃ A)) ↔ ∃(a ↦ (a ∈ A) ∧ (x ∈ a))
  Σ.left  (∃.witness (Tuple.left ([⋃]-membership {A = A} {x}) ([∃]-intro a ⦃ [∧]-intro ([∃]-intro iA) _ ⦄))) = iA
  Σ.right (∃.witness (Tuple.left ([⋃]-membership {A = A} {x}) ([∃]-intro a ⦃ [∧]-intro ([∃]-intro iA ⦃ aA ⦄) ([∃]-intro ia) ⦄))) = _⊆_.map (_≡_.right aA) ia
  ∃.proof (Tuple.left ([⋃]-membership {A = A} {x}) ([∃]-intro a ⦃ [∧]-intro ([∃]-intro iA ⦃ aA ⦄) ([∃]-intro ia ⦃ xa ⦄) ⦄)) = [≡]-transitivity-raw xa ([⊆]-with-elem (sub₂(_≡_)(_⊆_) aA) {ia})
  ∃.witness (Tuple.right ([⋃]-membership {A = A} {x}) ([∃]-intro (intro iA ia) ⦃ proof ⦄)) = elem(A)(iA)
  Tuple.left (∃.proof (Tuple.right ([⋃]-membership {A = A} {x}) ([∃]-intro (intro iA ia) ⦃ proof ⦄))) = [∈]-of-elem {A = A}
  ∃.witness (Tuple.right (∃.proof (Tuple.right ([⋃]-membership {A = A} {x}) ([∃]-intro (intro iA ia) ⦃ proof ⦄)))) = ia
  ∃.proof (Tuple.right (∃.proof (Tuple.right ([⋃]-membership {A = A} {x}) ([∃]-intro (intro iA ia) ⦃ proof ⦄)))) = proof

  module _ {A : Iset{ℓ}} where
    open import Relator.Equals.Proofs.Equivalence using ([≡]-equiv)
    instance _ = [≡]-equiv {T = Index(A)}

    module _ {P : Index(A) → Stmt{ℓ}} where
      indexFilter-elem-membershipₗ : ∀{i : Index(A)} → (elem(A)(i) ∈ indexFilter A P) ← P(i)
      Σ.left (∃.witness ((indexFilter-elem-membershipₗ {i = i}) pi)) = i
      Σ.right(∃.witness ((indexFilter-elem-membershipₗ {i = i}) pi)) = pi
      _≡_.left  (∃.proof (indexFilter-elem-membershipₗ pi)) = intro id [≡]-reflexivity-raw
      _≡_.right (∃.proof (indexFilter-elem-membershipₗ pi)) = intro id [≡]-reflexivity-raw

    module _
      ⦃ _ : Injective(elem A) ⦄ -- TODO: Is this satisfiable?
      {P : Index(A) → Stmt{ℓ}}
      ⦃ unaryRelator-P : UnaryRelator(P) ⦄
      where

      indexFilter-elem-membership : ∀{i : Index(A)} → (elem(A)(i) ∈ indexFilter A P) ↔ P(i)
      Tuple.left   indexFilter-elem-membership = indexFilter-elem-membershipₗ
      Tuple.right (indexFilter-elem-membership {i = i}) ([∃]-intro (intro iA PiA) ⦃ pp ⦄) = substitute₁(P) (injective(elem A) (symmetry(_≡_) pp)) PiA

  filter-elem-membership : ∀{A : Iset{ℓ}}{P} ⦃ _ : UnaryRelator(P) ⦄ {i : Index(A)} → (elem(A)(i) ∈ filter A P) ↔ P(elem(A)(i))
  Tuple.left  (filter-elem-membership {A = A}{P = P}) = indexFilter-elem-membershipₗ {A = A}{P = P ∘ elem(A)}
  Tuple.right (filter-elem-membership {P = P}) ([∃]-intro (intro iA PiA) ⦃ pp ⦄) = substitute₁(P) (symmetry(_≡_) pp) PiA

  filter-membership : ∀{A : Iset{ℓ}}{P} ⦃ _ : UnaryRelator(P) ⦄ {x : Iset{ℓ}} → (x ∈ filter A P) ↔ ((x ∈ A) ∧ P(x))
  ∃.witness (Tuple.left(filter-membership {P = P}) ([∧]-intro ([∃]-intro i ⦃ p ⦄) pb)) = intro i (substitute₁(P) p pb)
  ∃.proof   (Tuple.left(filter-membership) ([∧]-intro ([∃]-intro i ⦃ p ⦄) pb)) = p
  ∃.witness (Tuple.left (Tuple.right(filter-membership) ([∃]-intro (intro iA PiA) ⦃ pp ⦄))) = iA
  ∃.proof (Tuple.left (Tuple.right(filter-membership) ([∃]-intro (intro iA PiA) ⦃ pp ⦄))) = pp
  Tuple.right (Tuple.right(filter-membership {P = P}) ([∃]-intro (intro iA PiA) ⦃ pp ⦄)) = substitute₁(P) (symmetry(_≡_) pp) PiA

  mapSet-membership : ∀{A : Iset{ℓ}}{f} ⦃ _ : Function(f) ⦄ {y : Iset{ℓ}} → (y ∈ mapSet f(A)) ↔ ∃(x ↦ (x ∈ A) ∧ (y ≡ f(x)))
  ∃.witness (Tuple.left  (mapSet-membership)                         ([∃]-intro x ⦃ [∧]-intro xA fxy ⦄)) = [∃]-witness xA
  ∃.proof   (Tuple.left  (mapSet-membership {A = A} {f = f} {y = y}) ([∃]-intro x ⦃ [∧]-intro xA fxy ⦄)) =
    y                                   🝖[ _≡_ ]-[ fxy ]
    f(x)                                🝖[ _≡_ ]-[ congruence₁(f) ([∃]-proof xA) ]
    f(elem(A) ([∃]-witness xA))         🝖[ _≡_ ]-[]
    elem (mapSet f(A)) ([∃]-witness xA) 🝖[ _≡_ ]-end
  ∃.witness (Tuple.right (mapSet-membership {A = A}) ([∃]-intro iA)) = elem(A) iA
  Tuple.left  (∃.proof (Tuple.right (mapSet-membership {A = A}) ([∃]-intro iA ⦃ p ⦄))) = [∈]-of-elem {A = A} {ia = iA}
  Tuple.right (∃.proof (Tuple.right  mapSet-membership          ([∃]-intro iA ⦃ p ⦄))) = p

  open import Logic.Classical
  module _ ⦃ classical : ∀{ℓ}{P} → Classical{ℓ}(P) ⦄ where
    indexFilterBool-subset : ∀{A : Iset{ℓ}}{P} → (indexFilterBool A P ⊆ A)
    _⊇_.map indexFilterBool-subset (intro iA _) = iA
    _⊇_.proof (indexFilterBool-subset {ℓ = ℓ}{A = A}{P = P}) {intro iA (Lvl.up PiA)} =
      elem (indexFilterBool A P) (intro iA (Lvl.up PiA))                        🝖[ _≡_ ]-[]
      elem (indexFilter A (Lvl.Up ∘ IsTrue ∘ P)) (intro iA (Lvl.up PiA))        🝖[ _≡_ ]-[]
      elem A (Σ.left {B = Lvl.Up{ℓ₂ = ℓ} ∘ IsTrue ∘ P} (intro iA (Lvl.up PiA))) 🝖[ _≡_ ]-[]
      elem A iA                                                                 🝖[ _≡_ ]-end

    ℘-membershipₗ : ∀{A : Iset{ℓ}}{B : Iset{ℓ}} → (B ∈ ℘(A)) ← (B ⊆ A)
    ∃.witness (℘-membershipₗ {A = A}{B = B} BA) iA = decide(∃(iB ↦ Id(_⊆_.map BA iB) iA))
    _⊇_.map (_≡_.left (∃.proof (℘-membershipₗ {A = A} {B = B} _))) (intro iA (Lvl.up mapiBiA)) = [∃]-witness([↔]-to-[←] decide-is-true mapiBiA)
    _⊇_.proof (_≡_.left (∃.proof (℘-membershipₗ {ℓ = ℓ} {A = A} {B = B} BA))) {intro iA (Lvl.up mapiBiA)} =
      elem (elem (℘ A) f) (intro iA (Lvl.up mapiBiA))                              🝖[ _≡_ ]-[]
      elem (indexFilterBool A f) (intro iA (Lvl.up mapiBiA))                        🝖[ _≡_ ]-[]
      elem (indexFilter A (Lvl.Up ∘ IsTrue ∘ f)) (intro iA (Lvl.up mapiBiA))        🝖[ _≡_ ]-[]
      elem A (Σ.left {B = Lvl.Up{ℓ₂ = ℓ} ∘ IsTrue ∘ f} (intro iA (Lvl.up mapiBiA))) 🝖[ _≡_ ]-[]
      elem A iA                                                                     🝖[ _≡_ ]-[ [≡]-to-equivalence(congruence₁(elem A) ([∃]-proof emapiBiA)) ]-sym
      elem A (_⊆_.map BA ([∃]-witness emapiBiA)) 🝖[ _≡_ ]-[ symmetry(_≡_) (_⊆_.proof BA {[∃]-witness emapiBiA}) ]
      elem B ([∃]-witness emapiBiA)       🝖[ _≡_ ]-end
      where
        f = \iA → decide(∃(iB ↦ Id(_⊆_.map BA iB) iA))
        emapiBiA = [↔]-to-[←] decide-is-true mapiBiA
        open import Relator.Equals.Proofs.Equiv using ([≡]-to-equivalence)
    _⊇_.map (_≡_.right (∃.proof (℘-membershipₗ {A = A} {B = B} BA))) iB = intro (_⊆_.map BA iB) (Lvl.up ([↔]-to-[→] decide-is-true ([∃]-intro iB ⦃ intro ⦄)))
    _⊇_.proof (_≡_.right (∃.proof (℘-membershipₗ {A = A} {B = B} BA))) = _⊆_.proof BA

    ℘-membershipᵣ : ∀{A : Iset{ℓ}}{B : Iset{ℓ}} → (B ∈ ℘(A)) → (B ⊆ A)
    ℘-membershipᵣ ([∃]-intro witness ⦃ b≡indexFilterBool ⦄) = substitute₂ₗ(_⊆_) (symmetry(_≡_) b≡indexFilterBool) indexFilterBool-subset

    ℘-membership : ∀{A : Iset{ℓ}}{x : Iset{ℓ}} → (x ∈ ℘(A)) ↔ (x ⊆ A)
    ℘-membership = [↔]-intro ℘-membershipₗ ℘-membershipᵣ
