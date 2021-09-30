module Numeral.Integer.Relation.Order where

open import Functional
import      Lvl
import      Numeral.Natural.Relation.Order as ℕ
open import Numeral.Integer
open import Numeral.Integer.Oper
open import Relator.Ordering
open import Type

-- Inequalities/Comparisons
data _≤_ : ℤ → ℤ → Type{Lvl.𝟎} where
  pos : ∀{a b} → (a ℕ.≤ b) → ((+ₙ a) ≤ (+ₙ b))
  mix : ∀{a b} → (−𝐒ₙ(a)) ≤ (+ₙ b)
  neg : ∀{a b} → (a ℕ.≤ b) → ((−𝐒ₙ(b)) ≤ (−𝐒ₙ(a)))

data _<_ : ℤ → ℤ → Type{Lvl.𝟎} where
  pos : ∀{a b} → (a ℕ.< b) → ((+ₙ a) < (+ₙ b))
  mix : ∀{a b} → (−𝐒ₙ(a)) < (+ₙ b)
  neg : ∀{a b} → (a ℕ.< b) → ((−𝐒ₙ(b)) < (−𝐒ₙ(a)))

open From-[≤][<] (_≤_)(_<_) public



import      Data.Either as Either
import      Numeral.Natural as ℕ
import      Numeral.Natural.Relation.Order.Proofs as ℕ
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function
import      Structure.Relator.Ordering as Structure
open import Structure.Relator.Properties

instance
  [≤][−𝐒ₙ]-sub : (swap(_≤_) on₂ (−𝐒ₙ_)) ⊆₂ (ℕ._≤_)
  _⊆₂_.proof [≤][−𝐒ₙ]-sub (neg p) = p

instance
  [≤][+ₙ]-sub : ((_≤_) on₂ (+ₙ_)) ⊆₂ (ℕ._≤_)
  _⊆₂_.proof [≤][+ₙ]-sub (pos p) = p

instance
  [≤]-reflexivity : Reflexivity(_≤_)
  Reflexivity.proof [≤]-reflexivity {+ₙ  x} = pos (reflexivity(ℕ._≤_))
  Reflexivity.proof [≤]-reflexivity {−𝐒ₙ x} = neg (reflexivity(ℕ._≤_))

instance
  [≤]-transitivity : Transitivity(_≤_)
  Transitivity.proof [≤]-transitivity (pos p) (pos q) = pos(transitivity(ℕ._≤_) p q)
  Transitivity.proof [≤]-transitivity (neg p) (neg q) = neg(transitivity(ℕ._≤_) q p)
  Transitivity.proof [≤]-transitivity (neg p) mix     = mix
  Transitivity.proof [≤]-transitivity mix     (pos q) = mix

instance
  [≤]-antisymmetry : Antisymmetry(_≤_)(_≡_)
  Antisymmetry.proof [≤]-antisymmetry (pos {ℕ.𝟎}   {ℕ.𝟎}   p) (pos q) = [≡]-intro
  Antisymmetry.proof [≤]-antisymmetry (neg {ℕ.𝟎}   {ℕ.𝟎}   p) (neg q) = [≡]-intro
  Antisymmetry.proof [≤]-antisymmetry (pos {ℕ.𝐒 a} {ℕ.𝐒 b} p) (pos q) = congruence₁(+ₙ_)  (antisymmetry(ℕ._≤_)(_≡_) p q)
  Antisymmetry.proof [≤]-antisymmetry (neg {ℕ.𝐒 a} {ℕ.𝐒 b} p) (neg q) = congruence₁(−𝐒ₙ_) (antisymmetry(ℕ._≤_)(_≡_) q p)

instance
  [≤]-converseTotal : ConverseTotal(_≤_)
  ConverseTotal.proof [≤]-converseTotal {+ₙ  x} {+ₙ  y} = Either.map pos pos (converseTotal(ℕ._≤_))
  ConverseTotal.proof [≤]-converseTotal {+ₙ  x} {−𝐒ₙ y} = Either.Right mix
  ConverseTotal.proof [≤]-converseTotal {−𝐒ₙ x} {+ₙ  y} = Either.Left  mix
  ConverseTotal.proof [≤]-converseTotal {−𝐒ₙ x} {−𝐒ₙ y} = Either.map neg neg (converseTotal(ℕ._≤_))

instance
  [≤]-weakPartialOrder : Structure.Weak.PartialOrder(_≤_)
  [≤]-weakPartialOrder = record{}

instance
  [≤]-totalOrder : Structure.Weak.TotalOrder(_≤_)
  [≤]-totalOrder = record{}

{-
instance
  [+][⋅][≤]-orderedRing : let open Ring ⦃ … ⦄ in Ordered(_+_)(_⋅_)(_≤_)
  Ordered.[≤][+]ₗ-preserve [+][⋅][≤]-orderedRing = p where
    postulate p : ∀{x y z} → (x ≤ y) → ((x + z) ≤ (y + z))
    {-p {+ₙ x}    {+ₙ y}     {+ₙ  z} (pos xy) = pos {!!}
    p {−𝐒ₙ x}   {−𝐒ₙ y}    {−𝐒ₙ z} (neg xy) = neg {!!}
    p {+ₙ ℕ.𝟎}  {+ₙ ℕ.𝟎}   {−𝐒ₙ z} (pos xy) = reflexivity(_≤_)
    p {+ₙ ℕ.𝟎}  {+ₙ ℕ.𝐒 y} {−𝐒ₙ z} (pos xy) = {!!}
    p {+ₙ ℕ.𝐒 x} {+ₙ ℕ.𝐒 y}{−𝐒ₙ z} (pos xy) = {!!}
    p {.(−𝐒ₙ _)} {.(+ₙ _)} {+ₙ  z} mix = {!!}
    p {.(−𝐒ₙ _)} {.(+ₙ _)} {−𝐒ₙ z} mix = {!!}-}
  Ordered.[≤][⋅]-preserve-positive [+][⋅][≤]-orderedRing = p where
    p : ∀{x y} → (𝟎 ≤ x) → (𝟎 ≤ y) → (𝟎 ≤ (x ⋅ y))
    p {+ₙ ℕ.𝟎}   {+ₙ ℕ.𝟎}   (pos px) (pos py) = pos py
    p {+ₙ ℕ.𝟎}   {+ₙ ℕ.𝐒 y} (pos px) (pos py) = pos px
    p {+ₙ ℕ.𝐒 x} {+ₙ ℕ.𝟎}   (pos px) (pos py) = pos py
    p {+ₙ ℕ.𝐒 x} {+ₙ ℕ.𝐒 y} (pos px) (pos py) = pos ℕ.[≤]-minimum
-}
