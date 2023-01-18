module BidirectionalFunction where

open import Data.Tuple as Tuple using (_⨯_)
open import Function using (_←_)
import      Lvl
open import Type

infix 30 _↔_

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable A B C A₁ A₂ B₁ B₂ : Type{ℓ}

-- Bidirectional function type.
_↔_ : Type{ℓ₁} → Type{ℓ₂} → Type
X ↔ Y = (X ← Y) ⨯ (X → Y)
open module _↔_ {ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} (f : A ↔ B) = Tuple._⨯_ f
  using ()
  renaming (left to infixr 0 _$ₗ_ ; right to infixr 0 _$ᵣ_)
  public
open Tuple
  using ()
  renaming (_,_ to intro)
  public

import Functional as Fn

id : A ↔ A
id = intro Fn.id Fn.id

rev : (A ↔ B) ↔ (B ↔ A)
rev = intro Tuple.swap Tuple.swap

map : (A₁ ↔ A₂) → (B₁ ↔ B₂) → (A₁ ↔ B₁) ↔ (A₂ ↔ B₂)
map (intro aₗ aᵣ) (intro bₗ bᵣ) = intro
  (\(intro ba ab) → intro
    (aₗ Fn.∘ ba Fn.∘ bᵣ)
    (bₗ Fn.∘ ab Fn.∘ aᵣ)
  )
  (\(intro ba ab) → intro
    (aᵣ Fn.∘ ba Fn.∘ bₗ)
    (bᵣ Fn.∘ ab Fn.∘ aₗ)
  )

_∘_ : let _ = A in (B ↔ C) → (A ↔ B) → (A ↔ C)
f ∘ g = map id f $ᵣ g
infixl 10000 _∘_
