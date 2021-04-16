module Type.Category.IntensionalFunctionsCategory.LvlUpFunctor where

import Lvl
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Category
open import Structure.Category.Functor
open import Type
open import Type.Category.IntensionalFunctionsCategory

private variable ℓ₁ ℓ₂ : Lvl.Level

instance
  LvlUp-functor : Functor(typeIntensionalFnCategory)(typeIntensionalFnCategory)(Lvl.Up{ℓ₁}{ℓ₂})
  Functor.map           LvlUp-functor f(Lvl.up x) = Lvl.up(f(x))
  Functor.op-preserving LvlUp-functor = [≡]-intro
  Functor.id-preserving LvlUp-functor = [≡]-intro
