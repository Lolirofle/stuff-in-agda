module Formalization.RecursiveFunction where

import      Lvl
open import Data
open import Data.ListSized
open import Numeral.Finite
open import Numeral.Natural
open import Syntax.Number
open import Type{Lvl.𝟎}

-- Function(n) is a syntactic representation of recursive functions of type (ℕⁿ → ℕ).
-- The syntax
data Function : ℕ → Type where
  -- Base cases
  Base        : Function(0)
  Successor   : Function(1)
  Projection  : ∀{n : ℕ} → (i : 𝕟(n)) → Function(n)

  -- Inductive cases
  Composition : ∀{m n : ℕ} → Function(n) → List(Function(m))(n) → Function(m)
  Recursion   : ∀{n : ℕ} → Function(n) → Function(𝐒(𝐒(n))) → Function(𝐒(n))
  Minimization : ∀{n : ℕ} → Function(𝐒(n)) → Function(n)

Primitive : Type
Primitive = ℕ

module _ where
  open import Data.ListSized.Functions
  open import Functional
  open import Logic.Predicate
  open import Numeral.Natural.Relation.Order

  private variable m n   : ℕ
  private variable i     : 𝕟(n)
  private variable x v   : Primitive
  private variable xs vs : List(Primitive)(n)
  private variable f g   : Function(m)
  private variable fs gs : List(Function(m))(n)

  -- The operational semantics.
  data _$_⟹_ : ∀{m n} → List(Function(m))(n) → List(Primitive)(m) → List(Primitive)(n) → Type
  data _$_⟶_ : ∀{n} → Function(n) → List(Primitive)(n) → ℕ → Type where
    zero : (Base $ ∅ ⟶ 𝟎)
    succ : (Successor $ singleton(n) ⟶ 𝐒(n))
    proj : (Projection{n}(i) $ xs ⟶ index(i)(xs))
    comp : (f $ vs ⟶ v) → (gs $ xs ⟹ vs) → (Composition{m}{n} f gs $ xs ⟶ v)
    rec𝟎 : (f $ xs ⟶ v) → (Recursion f g $ (𝟎 ⊰ xs) ⟶ v)
    rec𝐒 : (Recursion f g $ (n ⊰ xs) ⟶ x) → (g $ (n ⊰ x ⊰ xs) ⟶ v) → (Recursion f g $ (𝐒(n) ⊰ xs) ⟶ v)
    min  : (f $ (n ⊰ xs) ⟶ 𝟎) → ∃{Obj = ℕ → ℕ}(k ↦ ∀{m} → (m < n) → (f $ (m ⊰ xs) ⟶ 𝐒(k(m)))) → (Minimization f $ xs ⟶ n)
  data _$_⟹_ where
    base : (∅ $ xs ⟹ ∅)
    step : (f $ xs ⟶ v) → (fs $ xs ⟹ vs) → ((f ⊰ fs) $ xs ⟹ (v ⊰ vs))

  -- TODO: The denotational semantics should use partial functions, but even if that was used, one needs to decide whether there is a 0 in an arbitrary function's range. This is not possible, I guess?

  open import Logic.Propositional
  open import Numeral.Natural.Relation.Order.Proofs
  open import Relator.Equals
  open import Relator.Equals.Proofs
  open import Structure.Operator
  open import Structure.Setoid.Uniqueness

  [$⟹]-deterministic : Unique(fs $ xs ⟹_)

  [$⟶]-deterministic : Unique(f $ xs ⟶_)
  [$⟶]-deterministic zero         zero = [≡]-intro
  [$⟶]-deterministic succ         succ = [≡]-intro
  [$⟶]-deterministic proj         proj = [≡]-intro
  [$⟶]-deterministic (comp p₁ p₂) (comp q₁ q₂) rewrite [$⟹]-deterministic p₂ q₂ = [$⟶]-deterministic p₁ q₁
  [$⟶]-deterministic (rec𝟎 p)     (rec𝟎 q) = [$⟶]-deterministic p q
  [$⟶]-deterministic (rec𝐒 p₁ p₂) (rec𝐒 q₁ q₂) rewrite [$⟶]-deterministic p₁ q₁ = [$⟶]-deterministic p₂ q₂
  [$⟶]-deterministic {x = x}{y = y} (min p₁ ([∃]-intro k₁ ⦃ p₂ ⦄)) (min q₁ ([∃]-intro k₂ ⦃ q₂ ⦄)) with [<]-trichotomy {x}{y}
  ... | [∨]-introₗ ([∨]-introₗ lt) with () ← [$⟶]-deterministic p₁ (q₂ lt)
  ... | [∨]-introₗ ([∨]-introᵣ eq) = eq
  ... | [∨]-introᵣ             gt  with () ← [$⟶]-deterministic q₁ (p₂ gt)

  [$⟹]-deterministic base base = [≡]-intro
  [$⟹]-deterministic (step p pl) (step q ql) = congruence₂(_⊰_) ([$⟶]-deterministic p q) ([$⟹]-deterministic pl ql)

  [$⟶]-not-total : ∃{Obj = Function(n)}(f ↦ ∀{xs} → ¬ ∃(f $ xs ⟶_))
  ∃.witness [$⟶]-not-total = Minimization (Composition Successor (singleton (Projection 0)))
  ∃.proof   [$⟶]-not-total ([∃]-intro _ ⦃ min (comp () _) _ ⦄)
