module Lvl.Proofs where

open import Data.Tuple as Tuple using ()
open import Logic.Predicate
open import Lvl
open import Sets.Setoid
open import Structure.Function.Domain
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T : Type{ℓ}

instance
  LvlUp-equiv : ⦃ _ : Equiv(T) ⦄ → Equiv(Lvl.Up{_}{ℓ}(T))
  Equiv._≡_ (LvlUp-equiv {ℓ = ℓ}) (up x) (up y) = Lvl.Up{_}{ℓ}(x ≡ y)
  Up.obj (Reflexivity.proof (Equivalence.reflexivity (Equiv.[≡]-equivalence LvlUp-equiv))) = reflexivity(_≡_)
  Up.obj (Symmetry.proof (Equivalence.symmetry (Equiv.[≡]-equivalence LvlUp-equiv)) (up p)) = symmetry(_≡_) p
  Up.obj (Transitivity.proof (Equivalence.transitivity (Equiv.[≡]-equivalence LvlUp-equiv)) (up p) (up q)) = transitivity(_≡_) p q

instance
  LvlUpObj-bijective : ⦃ _ : Equiv(T) ⦄ → Bijective(Lvl.Up.obj{ℓ₂ = ℓ}{T = T})
  Up.obj (∃.witness (Tuple.left (Bijective.proof LvlUpObj-bijective {y}))) = y
  ∃.proof (Tuple.left (Bijective.proof LvlUpObj-bijective)) = reflexivity(_≡_)
  Up.obj (Tuple.right (Bijective.proof LvlUpObj-bijective) p q) = transitivity(_≡_) p (symmetry(_≡_) q)