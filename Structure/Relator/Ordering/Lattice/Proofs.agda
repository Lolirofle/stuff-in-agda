module Structure.Relator.Ordering.Lattice.Proofs where

open import Logic.Propositional
import      Lvl
open import Sets.PredicateSet renaming (_≡_ to _≡ₛ_)
open import Structure.Relator.Ordering.Lattice
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}
private variable P Q : T → Type{ℓ}
private variable < : T → T → Type{ℓ}

rightBound-relation-sub : (P ⊇ Q) → (RightBound(<)(P) ⊆ RightBound(<)(Q))
rightBound-relation-sub sub (intro bound-p) = intro(\ ⦃ qx ⦄ → bound-p ⦃ sub qx ⦄)

rightBound-relation : (P ≡ₛ Q) → (RightBound(<)(P) ≡ₛ RightBound(<)(Q))
rightBound-relation eq = [⊇][⊆]-to-[≡]
  (\{x} → rightBound-relation-sub (\{x} → [≡]-to-[⊆] (\{x} → eq{x}) {x}) {x})
  (\{x} → rightBound-relation-sub (\{x} → [≡]-to-[⊇] (\{x} → eq{x}) {x}) {x})

top-relation : (P ≡ₛ Q) → (Top(<)(P) ≡ₛ Top(<)(Q))
top-relation eq = [↔]-intro
  (\(intro ⦃ qx ⦄ ⦃ min-q ⦄) → intro ⦃ [↔]-to-[←] eq qx ⦄ ⦃ [↔]-to-[←] (rightBound-relation eq) min-q ⦄)
  (\(intro ⦃ px ⦄ ⦃ min-p ⦄) → intro ⦃ [↔]-to-[→] eq px ⦄ ⦃ [↔]-to-[→] (rightBound-relation eq) min-p ⦄)
