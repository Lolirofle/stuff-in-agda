module Data.List.Relation.Quantification where

import      Lvl
open import Data.List
open import Logic
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable T A B : Type{ℓ}
private variable l l₁ l₂ : List(T)
private variable x y px py : T
private variable P : T → Stmt{ℓ}

-- TODO: How about this as an alternative definition?
-- module _ (P : T → Type{ℓ}) where
--   open import Type.Dependent
--   open Data.IndexedList(Σ T P){List(T)} using (IndexedList ; intro)
--
--   AllElements : List(T) → Stmt{Lvl.of(T) Lvl.⊔ ℓ}
--   AllElements = IndexedList(intro ∅ ((_⊰_) ∘ Σ.left))
data AllElements (P : T → Stmt{ℓ}) : List(T) → Stmt{Lvl.of(T) Lvl.⊔ ℓ} where
  ∅   : AllElements(P)(∅)
  _⊰_ : P(x) → AllElements(P)(l) → AllElements(P)(x ⊰ l)

data ExistsElement (P : T → Stmt{ℓ}) : List(T) → Stmt{Lvl.of(T) Lvl.⊔ ℓ} where
  •_ : P(x)                → ExistsElement(P)(x ⊰ l)
  ⊰_ : ExistsElement(P)(l) → ExistsElement(P)(x ⊰ l)

-- TODO: Maybe remove this and use AllElements with map₂ instead
data AllElements₂ (P : A → B → Stmt{ℓ}) : List(A) → List(B) → Stmt{Lvl.of(A) Lvl.⊔ Lvl.of(B) Lvl.⊔ ℓ} where
  ∅   : AllElements₂(P)(∅)(∅)
  _⊰_ : P(x)(y) → AllElements₂(P)(l₁)(l₂) → AllElements₂(P)(x ⊰ l₁)(y ⊰ l₂)

∀ₗᵢₛₜ : List(T) → (T → Stmt{ℓ}) → Stmt
∀ₗᵢₛₜ(l) P = AllElements P l

∃ₗᵢₛₜ : List(T) → (T → Stmt{ℓ}) → Stmt
∃ₗᵢₛₜ(l) P = ExistsElement P l

module _ {P : T → Type{ℓ}} where
  open import Logic.Propositional
  open import Structure.Relator.Equivalence
  import      Structure.Relator.Names as Names
  open import Structure.Relator.Properties
  open import Structure.Setoid

  data ExistsElementEquivalence : ExistsElement(P)(l) → ExistsElement(P)(l) → Stmt{Lvl.of(T) Lvl.⊔ ℓ} where
    use  : ExistsElementEquivalence{l = x ⊰ l}(• px)(• py)
    skip : ExistsElementEquivalence(px)(py) → ExistsElementEquivalence{l = x ⊰ l}(⊰ px)(⊰ py)

  instance
    ExistsElementEquivalence-equiv : Equiv(ExistsElement(P)(l))
    Equiv._≡_ ExistsElementEquivalence-equiv = ExistsElementEquivalence
    Equiv.equivalence ExistsElementEquivalence-equiv = intro ⦃ intro refl ⦄ ⦃ intro sym ⦄ ⦃ intro trans ⦄ where
      refl : Names.Reflexivity(ExistsElementEquivalence{l = l})
      refl{x = • _} = use
      refl{x = ⊰ p} = skip(refl{x = p})

      sym : Names.Symmetry(ExistsElementEquivalence{l = l})
      sym {x = • px} {y = • py} use      = use
      sym {x = ⊰ px} {y = ⊰ py} (skip p) = skip(sym{x = px}{y = py} p)

      trans : Names.Transitivity(ExistsElementEquivalence{l = l})
      trans {x = • px} {y = • py} {z = • pz} use      use      = use
      trans {x = ⊰ px} {y = ⊰ py} {z = ⊰ pz} (skip p) (skip q) = skip(trans {x = px} {y = py} {z = pz} p q)

module _ where
  open import Type.Properties.Singleton

  ExistsUniqueElement : (T → Stmt{ℓ}) → List(T) → Stmt
  ExistsUniqueElement P l = IsUnit(ExistsElement(P)(l)) ⦃ ExistsElementEquivalence-equiv ⦄

  ∃!ₗᵢₛₜ : List(T) → (T → Stmt{ℓ}) → Stmt
  ∃!ₗᵢₛₜ(l) P = ExistsUniqueElement P l
