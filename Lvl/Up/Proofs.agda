module Lvl.Up.Proofs where

open import Data.Tuple as Tuple using (_,_)
open import Logic.Predicate
open import Lvl
open import Structure.Setoid
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Operator.Properties
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Type
open import Type.Isomorphism

private variable ℓ ℓ₁ ℓ₂ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable T : Type{ℓ}

module _ ⦃ equiv : Equiv{ℓₑ₁}(T) ⦄ ⦃ equiv-LvlUp : Equiv{ℓₑ₂}(Lvl.Up{ℓ}(T)) ⦄ where
  instance
    LvlUpObj-bijective : ⦃ func : Function(Lvl.up) ⦄ → Bijective(Lvl.Up.obj)
    Tuple.left  (Bijective.proof LvlUpObj-bijective {y}) = [∃]-intro (Lvl.up(y)) ⦃ reflexivity(_≡_) ⦄
    Tuple.right (Bijective.proof LvlUpObj-bijective) p q = congruence₁(Lvl.up) (transitivity(_≡_) p (symmetry(_≡_) q))

  instance
    LvlUp-inverses : InversePair(Lvl.up , Lvl.Up.obj)
    Inverseᵣ.proof (InversePair.left  LvlUp-inverses)  = reflexivity(_≡_)
    Inverseᵣ.proof (InversePair.right LvlUp-inverses) = reflexivity(_≡_)

  LvlUp-id-isomorphism : (Lvl.Up(T) ≍ T)
  LvlUp-id-isomorphism = [∃]-intro(Lvl.up , Lvl.Up.obj)
