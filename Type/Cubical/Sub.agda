{-# OPTIONS --cubical #-}

module Type.Cubical.Sub where

import      Lvl
open import Type
open import Type.Cubical

private variable ℓ : Lvl.Level
private variable A : Type{ℓ}

{-# BUILTIN SUB Sub #-}

postulate inc : ∀{i : Interval} → (x : A) → Sub A i (\_ → x)
{-# BUILTIN SUBIN inc #-}

primitive primSubOut : ∀{i : Interval}{p : Interval.Partial i A} → Sub A i p → A



open import Function.Domains
open import Type.Cubical.Path.Equality
open import Type.Dependent.Sigma

postulate transpProof : (e : Interval → Type{ℓ}) → (i : Interval) → (a : Interval.Partial i (e Interval.𝟎)) → (b : (Sub (e Interval.𝟏) i (\o → Interval.transp(\i → e i) Interval.𝟎 (a o))) ) → Σ _ (Fiber (Interval.transp (\ i → e i) Interval.𝟎) (primSubOut b))
{-# BUILTIN TRANSPPROOF transpProof #-}
