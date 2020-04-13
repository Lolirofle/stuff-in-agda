module Type.Cubical.Equality where

open import Logic
open import Type
open import Type.Cubical
open import Type.Cubical.Path
open import Type.Cubical.Path.Proofs

_≡_ = Path

[≡]-reflexivity = constant-path

[≡]-symmetry = reverse-path

-- [≡]-transitivity = compose-path

[≡]-function = function-path

congruence₁ = map-path
