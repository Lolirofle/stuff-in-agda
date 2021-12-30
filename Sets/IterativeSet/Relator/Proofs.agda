module Sets.IterativeSet.Relator.Proofs where

import      Lvl
open import Data
open import Data.Boolean
open import Data.Boolean.Proofs
open import Data.Boolean.Stmt
open import Data.Boolean.Stmt.Logic
open import Data.Either as Either using (_‖_)
open import Data.Tuple as Tuple using ()
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural
open import Relator.Equals using () renaming (_≡_ to Id ; [≡]-intro to intro)
open import Sets.IterativeSet.Relator
open import Sets.IterativeSet
open import Structure.Setoid using (Equiv)
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
  open Iset

  instance
    [≡][⊆]-sub : (_≡_) ⊆₂ (_⊆_ {ℓ₁}{ℓ₂})
    [≡][⊆]-sub = intro [∧]-elimᵣ

  instance
    [≡][⊇]-sub : (_≡_) ⊆₂ (_⊇_ {ℓ₁}{ℓ₂})
    [≡][⊇]-sub = intro [∧]-elimₗ

  [≡]-reflexivity-raw : ∀{A : Iset{ℓ}} → (A ≡ A)
  [⊆]-reflexivity-raw : ∀{A : Iset{ℓ}} → (A ⊆ A)
  [⊇]-reflexivity-raw : ∀{A : Iset{ℓ}} → (A ⊇ A)

  [≡]-reflexivity-raw {A = A} = [∧]-intro [⊇]-reflexivity-raw [⊆]-reflexivity-raw
  [⊆]-reflexivity-raw {A = set elem} = intro id (\{i} → [≡]-reflexivity-raw {A = elem(i)})
  [⊇]-reflexivity-raw = [⊆]-reflexivity-raw

  [≡]-symmetry-raw : ∀{A B : Iset{ℓ}} → (A ≡ B) → (B ≡ A)
  [≡]-symmetry-raw {A = A}{B = B} ([∧]-intro l r) = [∧]-intro r l

  [≡]-transitivity-raw : ∀{A B C : Iset{ℓ}} → (A ≡ B) → (B ≡ C) → (A ≡ C)
  [⊆]-transitivity-raw : ∀{A B C : Iset{ℓ}} → (A ⊆ B) → (B ⊆ C) → (A ⊆ C)
  [⊇]-transitivity-raw : ∀{A B C : Iset{ℓ}} → (A ⊇ B) → (B ⊇ C) → (A ⊇ C)

  Tuple.left  ([≡]-transitivity-raw {A = A}{B = B}{C = C} ab bc) = [⊇]-transitivity-raw(Tuple.left ab) (Tuple.left bc)
  Tuple.right ([≡]-transitivity-raw {A = A}{B = B}{C = C} ab bc) = [⊆]-transitivity-raw(Tuple.right ab) (Tuple.right bc)

  _⊆_.map   ([⊆]-transitivity-raw {A = A} {B = B} {C = C} ab bc) = _⊆_.map bc ∘ _⊆_.map ab
  _⊆_.proof ([⊆]-transitivity-raw {A = set elemA} {B = set elemB} {C = set elemC} ab bc) {ia} = [≡]-transitivity-raw {A = elemA(ia)}{B = elemB (_⊆_.map ab ia)} {C = elemC((_⊆_.map bc)((_⊆_.map ab)(ia)))} (_⊆_.proof ab {ia}) (_⊆_.proof bc)

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
    [⊆]-antisymmetry = intro (swap [∧]-intro)
  instance
    [⊇]-antisymmetry : Antisymmetry(_⊇_ {ℓ})(_≡_)
    [⊇]-antisymmetry = intro [∧]-intro
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



  Iset-induction : ∀{P : Iset{ℓ₁} → Stmt{ℓ₂}} ⦃ _ : UnaryRelator(P) ⦄ → (∀{A : Iset{ℓ₁}} → (∀{a} → (a ∈ A) → P(a)) → P(A)) → (∀{A : Iset{ℓ₁}} → P(A))
  Iset-induction {P = P} p = Iset-index-induction (\{A} pp → p{A} (\{a} aA → substitute₁ₗ(P) ([∃]-proof aA) (pp{[∃]-witness aA})))



  [∈]-of-elem : ∀{A : Iset{ℓ}}{ia : Index(A)} → (elem(A)(ia) ∈ A)
  ∃.witness ([∈]-of-elem {ia = ia}) = ia
  ∃.proof    [∈]-of-elem = [≡]-reflexivity-raw

  Iset-intro-self-equality : ∀{A : Iset{ℓ}} → (set{Index = Index(A)}(elem(A)) ≡ A)
  _⊆_.map   (Tuple.left  Iset-intro-self-equality) = id
  _⊆_.map   (Tuple.right Iset-intro-self-equality) = id
  _⊆_.proof (Tuple.left  Iset-intro-self-equality) = [≡]-reflexivity-raw
  _⊆_.proof (Tuple.right Iset-intro-self-equality) = [≡]-reflexivity-raw

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
  Tuple.left  (Tuple.left ([≡]-membership {A = A} {B = B}) ab) = [↔]-to-[←] [⊇]-membership (Tuple.left ab)
  Tuple.right (Tuple.left ([≡]-membership {A = A} {B = B}) ab) = [↔]-to-[←] [⊆]-membership (Tuple.right ab)
  Tuple.left  (Tuple.right ([≡]-membership {A = A} {B = B}) xaxb) = [↔]-to-[→] [⊇]-membership ([↔]-to-[←] xaxb)
  Tuple.right (Tuple.right ([≡]-membership {A = A} {B = B}) xaxb) = [↔]-to-[→] [⊆]-membership ([↔]-to-[→] xaxb)



  [∈]ₗ-unaryRelation-raw : ∀{A₁ A₂ B : Iset{ℓ}} → (A₁ ≡ A₂) → (A₁ ∈ B) → (A₂ ∈ B)
  ∃.witness ([∈]ₗ-unaryRelation-raw pa ([∃]-intro i ⦃ p ⦄)) = i
  ∃.proof ([∈]ₗ-unaryRelation-raw pa ([∃]-intro i ⦃ p ⦄)) = [≡]-transitivity-raw ([≡]-symmetry-raw pa) p

  [∈]-binaryRelation-raw : ∀{A₁ A₂ B₁ B₂ : Iset{ℓ}} → (A₁ ≡ A₂) → (B₁ ≡ B₂) → ((A₁ ∈ B₁) → (A₂ ∈ B₂))
  [∈]-binaryRelation-raw {B₂ = B₂} pa pb = [∈]ₗ-unaryRelation-raw {B = B₂} pa ∘ [↔]-to-[←] [⊆]-membership (sub₂(_≡_)(_⊆_) pb)

  instance
    [∈]-binaryRelation : BinaryRelator(_∈_ {ℓ})
    [∈]-binaryRelation = BinaryRelator-introᵣ [∈]-binaryRelation-raw

  instance
    [⊆]-binaryRelator : BinaryRelator(_⊆_ {ℓ}{ℓ})
    [⊆]-binaryRelator = BinaryRelator-introᵣ \p1 p2 ps → sub₂(_≡_)(_⊇_) p1 🝖 ps 🝖 sub₂(_≡_)(_⊆_) p2
