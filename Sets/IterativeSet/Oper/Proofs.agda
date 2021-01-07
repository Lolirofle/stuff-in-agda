module Sets.IterativeSet.Oper.Proofs where

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
open import Sets.IterativeSet.Oper
open import Sets.IterativeSet.Relator
open import Sets.IterativeSet.Relator.Proofs
open import Sets.IterativeSet
open import Structure.Function.Domain
open import Structure.Function
open import Structure.Relator.Properties
open import Structure.Relator
open import Syntax.Function
open import Syntax.Transitivity
open import Type.Dependent
open import Type.Properties.Decidable
open import Type.Properties.Decidable.Proofs

module _ where
  private variable {ℓ ℓ₁ ℓ₂} : Lvl.Level
  open Iset

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
  Σ.right (∃.witness (Tuple.left ([⋃]-membership {A = A} {x}) ([∃]-intro a ⦃ [∧]-intro ([∃]-intro iA ⦃ aA ⦄) ([∃]-intro ia) ⦄))) = _⊆_.map (Tuple.right aA) ia
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
      Tuple.left  (∃.proof (indexFilter-elem-membershipₗ pi)) = intro id [≡]-reflexivity-raw
      Tuple.right (∃.proof (indexFilter-elem-membershipₗ pi)) = intro id [≡]-reflexivity-raw

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
    instance _ = classical-to-decidable
    instance _ = classical-to-decider

    indexFilterBool-subset : ∀{A : Iset{ℓ}}{P} → (indexFilterBool A P ⊆ A)
    _⊇_.map indexFilterBool-subset (intro iA _) = iA
    _⊇_.proof (indexFilterBool-subset {ℓ = ℓ}{A = A}{P = P}) {intro iA (Lvl.up PiA)} =
      elem (indexFilterBool A P) (intro iA (Lvl.up PiA))                   🝖[ _≡_ ]-[]
      elem (indexFilter A (Lvl.Up ∘ IsTrue ∘ P)) (intro iA (Lvl.up PiA))   🝖[ _≡_ ]-[]
      elem A (Σ.left {B = Lvl.Up{ℓ} ∘ IsTrue ∘ P} (intro iA (Lvl.up PiA))) 🝖[ _≡_ ]-[]
      elem A iA                                                            🝖[ _≡_ ]-end

    ℘-membershipₗ : ∀{A : Iset{ℓ}}{B : Iset{ℓ}} → (B ∈ ℘(A)) ← (B ⊆ A)
    ∃.witness (℘-membershipₗ {A = A}{B = B} BA) iA = decide(0)(∃(iB ↦ Id(_⊆_.map BA iB) iA))
    _⊇_.map (Tuple.left (∃.proof (℘-membershipₗ {A = A} {B = B} _))) (intro iA (Lvl.up mapiBiA)) = [∃]-witness([↔]-to-[←] decider-true mapiBiA)
    _⊇_.proof (Tuple.left (∃.proof (℘-membershipₗ {ℓ = ℓ} {A = A} {B = B} BA))) {intro iA (Lvl.up mapiBiA)} =
      elem (elem (℘ A) f) (intro iA (Lvl.up mapiBiA))                          🝖[ _≡_ ]-[]
      elem (indexFilterBool A f) (intro iA (Lvl.up mapiBiA))                   🝖[ _≡_ ]-[]
      elem (indexFilter A (Lvl.Up ∘ IsTrue ∘ f)) (intro iA (Lvl.up mapiBiA))   🝖[ _≡_ ]-[]
      elem A (Σ.left {B = Lvl.Up{ℓ} ∘ IsTrue ∘ f} (intro iA (Lvl.up mapiBiA))) 🝖[ _≡_ ]-[]
      elem A iA                                                                🝖[ _≡_ ]-[ [≡]-to-equivalence(congruence₁(elem A) ([∃]-proof emapiBiA)) ]-sym
      elem A (_⊆_.map BA ([∃]-witness emapiBiA))                               🝖[ _≡_ ]-[ _⊆_.proof BA {[∃]-witness emapiBiA} ]-sym
      elem B ([∃]-witness emapiBiA)                                            🝖[ _≡_ ]-end
      where
        f = \iA → decide(0)(∃(iB ↦ Id(_⊆_.map BA iB) iA))
        emapiBiA = [↔]-to-[←] decider-true mapiBiA
        open import Relator.Equals.Proofs.Equiv using ([≡]-to-equivalence)
    _⊇_.map (Tuple.right (∃.proof (℘-membershipₗ {A = A} {B = B} BA))) iB = intro (_⊆_.map BA iB) (Lvl.up ([↔]-to-[→] decider-true ([∃]-intro iB ⦃ intro ⦄)))
    _⊇_.proof (Tuple.right (∃.proof (℘-membershipₗ {A = A} {B = B} BA))) = _⊆_.proof BA

    ℘-membershipᵣ : ∀{A : Iset{ℓ}}{B : Iset{ℓ}} → (B ∈ ℘(A)) → (B ⊆ A)
    ℘-membershipᵣ ([∃]-intro witness ⦃ b≡indexFilterBool ⦄) = substitute₂ₗ(_⊆_) (symmetry(_≡_) b≡indexFilterBool) indexFilterBool-subset

    ℘-membership : ∀{A : Iset{ℓ}}{x : Iset{ℓ}} → (x ∈ ℘(A)) ↔ (x ⊆ A)
    ℘-membership = [↔]-intro ℘-membershipₗ ℘-membershipᵣ
