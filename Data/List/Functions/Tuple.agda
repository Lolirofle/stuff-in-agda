module Data.List.Functions.Tuple where

open import BidirectionalFunction
import      Lvl
open import Data.List
import      Data.List.Functions as List
import      Data.List.FunctionsProven as ListDep
open import Data.List.Relation.Quantification
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Type
open import Type.Dependent
import      Type.Dependent.FunctionsΣ as Σ

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T A A₁ A₂ B B₁ B₂ Result : Type{ℓ}
private variable P : T → Type{ℓ}

transpose₂ : (List(A) ⨯ List(B)) ↔ List(A ⨯ B)
Tuple.left  transpose₂ = List.foldᵣ(\(a , b) (la , lb) → (a ⊰ la , b ⊰ lb)) (∅ , ∅)
Tuple.right transpose₂ = Tuple.uncurry(List.map₂(_,_) (const ∅) (const ∅))

transposeΣ : Σ(List T) (AllElements P) ↔ List(Σ T P)
Tuple.left  transposeΣ = List.foldᵣ(\(intro a b) (intro la lb) → intro (a ⊰ la) (b ⊰ lb)) (intro ∅ ∅)
Tuple.right transposeΣ = Σ.elim(ListDep.map intro)
