{-# OPTIONS --cubical #-}

module Type.Cubical.Isomorphism.Proofs where

open import BidirectionalFunction
open import Logic.Predicate
import      Lvl
open import Structure.Function.Domain
open import Type
open import Type.Cubical
open import Type.Cubical.Isomorphism
open import Type.Cubical.Path.Equality

-- Similar to Type.Cubical.Path.Proofs.interval-predicate₀-pathP, but for type isomorphisms.
-- Used in Type.Cubical.Path.Univalence.type-extensionality.
interval-predicate-isomorphism : {ℓ : Interval → Lvl.Level} (P : (i : Interval) → Type{ℓ(i)}) → (P(Interval.𝟎) ≍ P(Interval.𝟏))
interval-predicate-isomorphism P = [∃]-intro f where
  f : P(Interval.𝟎) ↔ P(Interval.𝟏)
  f = intro
    (Interval.transp(\i → P(Interval.flip i)) Interval.𝟎)
    (Interval.transp P Interval.𝟎)

  p0i : ∀{i} → P(Interval.𝟎) → P(i)
  p0i{i} = Interval.transp(\j → P(Interval.min i j)) (Interval.flip i)

  p1i : ∀{i} → P(Interval.𝟏) → P(i)
  p1i{i} = Interval.transp(\j → P(Interval.max i (Interval.flip j))) i

  instance
    inv : InversePair f
    InversePair.left inv = intro \{p1} i → Interval.comp P 
      (\j → \{
        (i = Interval.𝟎) → p0i(f $ₗ p1) ;
        (i = Interval.𝟏) → p1i p1
      })
      (f $ₗ p1)
    InversePair.right inv = intro \{p0} i → Interval.comp (\i → P(Interval.flip i))
      (\j → \{
        (i = Interval.𝟎) → p1i(f $ᵣ p0) ;
        (i = Interval.𝟏) → p0i p0
      })
      (f $ᵣ p0)
