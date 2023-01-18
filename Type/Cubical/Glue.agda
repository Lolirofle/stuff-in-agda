{-# OPTIONS --cubical #-}

module Type.Cubical.Glue where

import      Lvl
open import Type
open import Type.Cubical
open import Type.Cubical.Isomorphism

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level

-- TODO: Write explanations for these
primitive primGlue : (A : Type{ℓ₁}) → ∀{i : Interval} → (T : Interval.Partial i (Type{ℓ₂})) → (e : Interval.PartialP i (\o → T(o) ≍ A)) → Type{ℓ₂}
primitive primFaceForall : (Interval → Interval) → Interval
primitive prim^glue : ∀{A : Type{ℓ}}{i : Interval}{T : Interval.Partial i (Type{ℓ₂})}{e : Interval.PartialP i (\o → T(o) ≍ A)} → (t : Interval.PartialP i T) → (a : A) → primGlue A T e
primitive prim^unglue : ∀{A : Type{ℓ}}{i : Interval}{T : Interval.Partial i (Type{ℓ₂})}{e : Interval.PartialP i (\o → T(o) ≍ A)} → primGlue A T e → A
