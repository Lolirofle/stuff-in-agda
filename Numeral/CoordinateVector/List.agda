module Numeral.CoordinateVector.List where

open import Data.List
import      Data.List.Functions as List
open import Functional
import      Lvl
open import Numeral.Finite
open import Numeral.Finite.Relation.Order using () renaming (_≡_ to _≡f_)
open import Numeral.CoordinateVector as Vector using (Vector)
open import Numeral.Natural
open import Numeral.Natural.Induction
open import Type
open import Type.Identity
open import Type.Identity.Proofs
open import Structure.Function
open import Structure.Relator.Properties
open import Structure.Setoid

private variable ℓ ℓₑ : Lvl.Level
private variable T A B : Type{ℓ}
private variable d : ℕ
private variable n n₁ n₂ : 𝕟(d)
private variable v : A → B

list : Vector d T → List T
list{d = d} = ℕ-elim(\d → Vector d _ → List _) (const ∅) (\_ prev f → f(𝟎) ⊰ prev(f ∘ 𝐒)) d

list-length-is-dim : Id (List.length(list v)) (Vector.dim v)
list-length-is-dim {d = 𝟎}  {v = v} = intro
list-length-is-dim {d = 𝐒 d}{v = v} = congruence₁ ⦃ _ ⦄ ⦃ _ ⦄ (𝐒) ⦃ Id-to-function ⦃ Id-equiv ⦄ ⦄ (list-length-is-dim{d = d}{v = Vector.tail v})

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  list-index-is-proj : (n₁ ≡f n₂) → (List.index(list{T = T} v) n₁ ≡ Vector.proj v n₂)
  list-index-is-proj {𝐒 _}    {v = v}{n₁ = 𝟎}   {n₂ = 𝟎}    eq = reflexivity(_≡_)
  list-index-is-proj {𝐒(𝐒 d₂)}{v = v}{n₁ = 𝐒 n₁}{n₂ = 𝐒 n₂} eq = list-index-is-proj {𝐒 d₂}{v = Vector.tail v}{n₁ = n₁}{n₂ = n₂} eq
