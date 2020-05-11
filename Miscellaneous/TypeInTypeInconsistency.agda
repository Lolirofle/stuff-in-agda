{-# OPTIONS --type-in-type #-}

-- Also called "Girard's paradox" or "Russell's paradox".
module Miscellaneous.TypeInTypeInconsistency where

data ISet : Set where
  set : ∀{I : Set} → (I → ISet) → ISet

open import Data.Tuple as Tuple using ()
open import Logic.Predicate
open import Logic.Propositional
open import Functional
import      Structure.Relator.Names as Names
open import Structure.Relator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Relator.Proofs
open import Structure.Setoid.WithLvl using (Equiv)
open import Syntax.Transitivity

_≡_ : ISet → ISet → Set
_∈_ : ISet → ISet → Set
_∉_ : ISet → ISet → Set

set {Ia} a ≡ set {Ib} b = ∃{Obj = Ib → Ia}(f ↦ ∀{ib} → (a(f(ib)) ≡ b(ib))) ∧ ∃{Obj = Ia → Ib}(f ↦ ∀{ia} → (a(ia) ≡ b(f(ia))))
a ∈ set(b) = ∃(ib ↦ (a ≡ b(ib)))
_∉_ = (¬_) ∘₂ (_∈_)

instance
  [≡]-reflexivity : Reflexivity(_≡_)
  [≡]-reflexivity = intro p where
    p : Names.Reflexivity(_≡_)
    p {set a} = [∧]-intro ([∃]-intro id ⦃ p ⦄) ([∃]-intro id ⦃ p ⦄)

instance
  [≡]-symmetry : Symmetry(_≡_)
  [≡]-symmetry = intro p where
    p : Names.Symmetry(_≡_)
    p {set a}{set b} ([∧]-intro l r) = [∧]-intro ([∃]-map-proof (\eq {i} → p(eq{i})) r) (([∃]-map-proof (\eq {i} → p(eq{i})) l))

instance
  [≡]-transitivity : Transitivity(_≡_)
  [≡]-transitivity = intro p where
    p : Names.Transitivity(_≡_)
    p {set x} {set y} {set z} ([↔]-intro ([∃]-intro fyx ⦃ yx ⦄) ([∃]-intro fxy ⦃ xy ⦄)) ([↔]-intro ([∃]-intro fzy ⦃ zy ⦄) ([∃]-intro fyz ⦃ yz ⦄)) = [∧]-intro ([∃]-intro (fyx ∘ fzy) ⦃ p yx zy ⦄) ([∃]-intro (fyz ∘ fxy) ⦃ p xy yz ⦄)

instance
  [≡]-equivalence : Equivalence(_≡_)
  [≡]-equivalence = intro

instance
  [≡]-equiv : Equiv(ISet)
  Equiv._≡_         [≡]-equiv = (_≡_)
  Equiv.equivalence [≡]-equiv = [≡]-equivalence

instance
  [∈]-unaryOperatorₗ : ∀{b} → UnaryRelator(_∈ b)
  UnaryRelator.substitution ([∈]-unaryOperatorₗ {set b}) {a₁} {a₂} a1a2 = [∃]-map-proof (symmetry(_≡_) a1a2 🝖_)

instance
  [∈]-unaryOperatorᵣ : ∀{a} → UnaryRelator(a ∈_)
  UnaryRelator.substitution ([∈]-unaryOperatorᵣ {a}) {set b₁} {set b₂} ([∧]-intro _ ([∃]-intro fb1b2 ⦃ b1b2 ⦄)) ([∃]-intro ib₁ ⦃ p ⦄) = [∃]-intro (fb1b2(ib₁)) ⦃ p 🝖 b1b2 ⦄

instance
  [∈]-binaryOperator : BinaryRelator(_∈_)
  [∈]-binaryOperator = binaryRelator-from-unaryRelator

NotSelfContaining : ISet
NotSelfContaining = set{∃(a ↦ (a ∉ a))} [∃]-witness

NotSelfContaining-membership : ∀{x} → (x ∈ NotSelfContaining) ↔ (x ∉ x)
NotSelfContaining-membership = [↔]-intro l r where
  l : ∀{x} → (x ∈ NotSelfContaining) ← (x ∉ x)
  ∃.witness (l {x} xin) = [∃]-intro x ⦃ xin ⦄
  ∃.proof   (l {x} xin) = reflexivity(_≡_)

  r : ∀{x} → (x ∈ NotSelfContaining) → (x ∉ x)
  r {x} ([∃]-intro ([∃]-intro witness ⦃ nxinx ⦄) ⦃ p ⦄) xinx = nxinx(substitute₂(_∈_) p p xinx)

NotSelfContaining-self : (NotSelfContaining ∈ NotSelfContaining)
∃.witness NotSelfContaining-self = [∃]-intro NotSelfContaining ⦃ \{s@([∃]-intro ([∃]-intro _ ⦃ p ⦄) ⦃ b ⦄) → p(substitute₂(_∈_) b b s)} ⦄
∃.proof NotSelfContaining-self = [∧]-intro ([∃]-intro id ⦃ reflexivity(_≡_) ⦄) ([∃]-intro id ⦃ reflexivity(_≡_) ⦄)

paradox : ⊥
paradox = [↔]-to-[→] NotSelfContaining-membership NotSelfContaining-self NotSelfContaining-self
