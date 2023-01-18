module Data.Wrap where

open import Type

record Wrap{ℓ}(T : Type{ℓ}) : Type{ℓ} where
  constructor wrap
  eta-equality
  field obj : T



import      Lvl

private variable ℓ : Lvl.Level
private variable T A B : Type{ℓ}



open import BidirectionalFunction as Bi using (_↔_ ; intro ; _$ᵣ_)
open import Functional 

wrapper : Wrap(T) ↔ T
wrapper = intro wrap Wrap.obj

map : (A → B) → (Wrap(A) → Wrap(B))
map f = wrap ∘ f ∘ Wrap.obj

bimap : (A ↔ B) ↔ (Wrap(A) ↔ Wrap(B))
bimap = Bi.rev $ᵣ Bi.map wrapper wrapper



open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function
open import Structure.Function.Domain
-- open import Structure.Operator.Properties
-- open import Structure.Relator
-- open import Structure.Relator.Properties

instance
  wrapper-inverse : InversePair(wrapper{T = T})
  wrapper-inverse = intro ⦃ left = intro [≡]-intro ⦄ ⦃ right = intro [≡]-intro ⦄

instance
  wrap-injectivity : Injective(wrap{T = T})
  wrap-injectivity = intro(congruence₁(Wrap.obj))

instance
  obj-injectivity : Injective(Wrap.obj{T = T})
  obj-injectivity = intro(congruence₁(wrap))

{- 
test : ∀{f : Type{ℓ} → Type{ℓ}} → (f(Wrap(T)) ≡ Wrap(f(T)))
test {ℓ} {T} {f} = {!!}

Wrap-injectivity : (Wrap(A) ≡ Wrap(B)) → (A ≡ B)
Wrap-injectivity eq = [≡]-unsubstitution \{f} fa → {!!}
-}
