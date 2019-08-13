module Data.Tuple.Function where

open import Data
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Type

module _ {ℓ₁ ℓ₂ ℓ₃} {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} {T₃ : Type{ℓ₃}} where
  _,⃝_ : (T₁ → T₂) → (T₁ → T₃) → (T₁ → (T₂ ⨯ T₃))
  _,⃝_ f g x = (f(x) , g(x))

  left : (T₁ → (T₂ ⨯ T₃)) → (T₁ → T₂)
  left =  Tuple.left ∘_

  right : (T₁ → (T₂ ⨯ T₃)) → (T₁ → T₃)
  right =  Tuple.right ∘_
