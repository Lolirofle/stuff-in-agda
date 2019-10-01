open import Type

module ReductionSystem {ℓ₁ ℓ₂} {Expr : Type{ℓ₁}} (_⟶_ : Expr → Expr → Type{ℓ₂}) where

import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Relator.Equals
open import Syntax.Function

-- The relation (_⟶_) is a function on the left argument.
Deterministic = ∀{a b c : Expr} → (a ⟶ b) → (a ⟶ c) → (b ≡ c)

-- An expression is reducible when there is an expression it can reduce to.
Reducible : Expr → Type
Reducible(a) = ∃(a ⟶_)

-- An expression is in normal form when it is irreducible (cannot be reduced any further).
NormalForm : Expr → Type
NormalForm(a) = ∀{b : Expr} → ¬(a ⟶ b)

-- Reflexive-transitive closure of a relation
data Star : Expr → Expr → Type{ℓ₁ Lvl.⊔ ℓ₂} where
  reflexivity : ∀{a} → (Star a a)
  closure : ∀{a b c} → (a ⟶ b) → (Star b c) → (Star a c)

Star-intro : ∀{a b} → (a ⟶ b) → (Star a b)
Star-intro ab = closure ab Star.reflexivity

Star-transitivity : ∀{a b c} → (Star a b) → (Star b c) → (Star a c)
Star-transitivity reflexivity                sbc  = sbc
Star-transitivity (closure ab sbb1) sb1c = closure ab (Star-transitivity sbb1 sb1c)

Normal-unique-Star : ∀{a} → NormalForm(a) → ∀{b} → Star a b → (a ≡ b)
Normal-unique-Star na reflexivity = [≡]-intro
Normal-unique-Star na (closure ab1 sb1b) = [⊥]-elim(na ab1)

-- A reduction system is normalizing when all expressions in the language have a normal form.
Normalizing = ∃{Obj = Expr → Expr} (normal ↦ ∀{e} → (Star e (normal e)) ∧ NormalForm(normal e))

-- Note: This is called path because of the interpretation that a binary relation (A → A → Set) is a graph
data Path : Expr → Expr → Type{ℓ₁ Lvl.⊔ ℓ₂} where
  reflexivity  : ∀{a} → Path a a
  super : ∀{a b} → (a ⟶ b) → Path a b
  transitivity : ∀{a b c} → Path a b → Path b c → Path a c

-- Both a and b reduce to the same expresion
-- TODO: What is Joinable?
CommonReduct : Expr → Expr → Type
CommonReduct a b = ∃(c ↦ (Star a c) ∧ (Star b c))

-- An expression is confluent when all its reducts have a common reduct
Confluent : Expr → Type
Confluent a = ∀{b c} → (a ⟶ b) → (a ⟶ c) → CommonReduct b c

-- confluent-to-equivalence : Confluent → Equivalence(CommonReduct)

-- Terminating = WellFounded ∘ converse

module _ (det : Deterministic) where
  -- Frege thing
  deterministic-dichotomy : ∀{a b c} → (Star a b) → (Star a c) → (Star b c) ∨ (Star c b)
  deterministic-dichotomy reflexivity ac = [∨]-introₗ ac
  deterministic-dichotomy (ab @ (closure _ _)) reflexivity = [∨]-introᵣ ab
  deterministic-dichotomy (closure ab2 b) (closure ab3 ac) with det ab2 ab3
  ... | [≡]-intro = deterministic-dichotomy b ac

  -- Normal(b) → Normal(c) → (Star a b) → (Star a c) → (b ≡ c)
