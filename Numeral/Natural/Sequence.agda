module Numeral.Natural.Sequence where

import      Lvl
open import Data
open import Data.Either as Either using (_‖_)
open import Data.Either.Proofs
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Data.Tuple.Proofs
open import Functional
open import Function.Proofs
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.DivMod.Proofs
open import Numeral.Natural.Oper.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
import      Structure.Function.Names as Names
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable A : Type{ℓ}
private variable B : Type{ℓ}

-- Interleaves two sequences into one, alternating between the elements from each sequence.
interleave : (ℕ → A) → (ℕ → B) → (ℕ → (A ‖ B))
interleave af bf 𝟎        = Either.Left(af(𝟎))
interleave af bf (𝐒 𝟎)    = Either.Right(bf(𝟎))
interleave af bf (𝐒(𝐒 n)) = interleave (af ∘ 𝐒) (bf ∘ 𝐒) n

-- Alternative forms:
--   pairIndexing a b = a + (∑(𝕟(a + b)) (i ↦ 𝕟-to-ℕ(i)))
--   pairIndexing a b = a + ((a + b) * (a + b + 1) / 2)
-- Example:
--   Horizontal axis is `a` starting from 0.
--   Vertical axis is `b` starting from 0.
--   Cells are `pairIndexing a b`.
--    0, 1, 3, 6,10,15
--    2, 4, 7,11,16,..
--    5, 8,12,17,   ..
--    9,13,18,      ..
--   14,19,         ..
--   20,.. .. .. .. ..
-- Termination:
--   Decreases `a` until 0 while at the same time increases `b` (So `b` is at most `a`).
--   Then the arguments is swapped, but using the predecessor of `b`.
--   This means that `b` will eventually reach 0.
{-# TERMINATING #-}
pairIndexing : ℕ → ℕ → ℕ
pairIndexing 𝟎     𝟎     = 𝟎
pairIndexing (𝐒 a) 𝟎     = 𝐒(pairIndexing 𝟎 a)
{-# CATCHALL #-}
pairIndexing a     (𝐒 b) = 𝐒(pairIndexing (𝐒 a) b)

-- A sequence which fills a discrete two dimensional grid (a space bounded in two directions and infinite in the other two).
-- It is the inverse of an uncurried `pairIndexing`.
-- Example:
--   •-→-• ↗→• ↗→•
--     ↙ ↗ ↙ ↗ ↙
--   •→↗ • ↗ •   •
--     ↙ ↗ ↙
--   •→↗ •   •   •
diagonalFilling : ℕ → (ℕ ⨯ ℕ)
diagonalFilling 𝟎      = (𝟎 , 𝟎)
diagonalFilling (𝐒(n)) with diagonalFilling n
... | (𝟎    , b) = (𝐒(b) , 0)
... | (𝐒(a) , b) = (a , 𝐒(b))



private variable af : ℕ → A
private variable bf : ℕ → B

pairIndexing-def3 : ∀{a b} → (pairIndexing a (𝐒 b) ≡ 𝐒(pairIndexing (𝐒 a) b))
pairIndexing-def3 {𝟎}   {b} = [≡]-intro
pairIndexing-def3 {𝐒 a} {b} = [≡]-intro

{-# TERMINATING #-}
pairIndexing-inverseₗ : Inverseₗ(Tuple.uncurry pairIndexing)(diagonalFilling)
pairIndexing-inverseₗ = intro proof where
  proof : Names.Inverses(diagonalFilling)(Tuple.uncurry pairIndexing)
  proof {𝟎    , 𝟎}    = [≡]-intro
  proof {𝐒(a) , 𝟎}    with diagonalFilling(pairIndexing 𝟎 a) | proof {𝟎 , a}
  ... | 𝟎    , 𝟎    | [≡]-intro = [≡]-intro
  ... | 𝟎    , 𝐒(d) | [≡]-intro = [≡]-intro
  ... | 𝐒(c) , 𝟎    | ()
  ... | 𝐒(c) , 𝐒(d) | ()
  {-# CATCHALL #-}
  proof {a    , 𝐒(b)} rewrite pairIndexing-def3 {a}{b} with diagonalFilling(pairIndexing (𝐒(a)) b) | proof {𝐒(a) , b}
  ... | 𝟎    , 𝟎    | ()
  ... | 𝟎    , 𝐒(d) | ()
  ... | 𝐒(c) , 𝟎    | [≡]-intro = [≡]-intro
  ... | 𝐒(c) , 𝐒(d) | [≡]-intro = [≡]-intro

pairIndexing-inverseᵣ : Inverseᵣ(Tuple.uncurry pairIndexing)(diagonalFilling)
pairIndexing-inverseᵣ = intro proof where
  proof : Names.Inverses(Tuple.uncurry pairIndexing)(diagonalFilling)
  proof {𝟎}    = [≡]-intro
  proof {𝐒(n)} with diagonalFilling n | proof {n}
  ... | (𝟎    , b) | q = congruence₁(𝐒) q
  ... | (𝐒(a) , b) | q rewrite pairIndexing-def3 {a}{b} = congruence₁(𝐒) q

instance
  pairIndexing-bijective : Bijective(Tuple.uncurry pairIndexing)
  pairIndexing-bijective = invertible-to-bijective ⦃ inver = [∃]-intro diagonalFilling ⦃ [∧]-intro [≡]-function ([∧]-intro pairIndexing-inverseₗ pairIndexing-inverseᵣ) ⦄ ⦄

interleave-left : ∀{n} → (interleave af bf (2 ⋅ n) ≡ Either.Left(af(n)))
interleave-left {n = 𝟎}   = [≡]-intro
interleave-left {n = 𝐒 n} = interleave-left {n = n}

interleave-right : ∀{n} → (interleave af bf (𝐒(2 ⋅ n)) ≡ Either.Right(bf(n)))
interleave-right {n = 𝟎}   = [≡]-intro
interleave-right {n = 𝐒 n} = interleave-right {n = n}


interleave-values : ∀{n} → (interleave af bf n ≡ Either.Left(af(n ⌊/⌋ 2))) ∨ (interleave af bf n ≡ Either.Right(bf(n ⌊/⌋ 2)))
interleave-values                    {n = 𝟎}      = [∨]-introₗ [≡]-intro
interleave-values                    {n = 𝐒 𝟎}    = [∨]-introᵣ [≡]-intro
interleave-values {af = af}{bf = bf} {n = 𝐒(𝐒 n)} = interleave-values {af = af ∘ 𝐒}{bf = bf ∘ 𝐒} {n = n}

interleave-left-args : ⦃ _ : Injective(af) ⦄ → ∀{m n} → (interleave af bf m ≡ Either.Left(af(n))) ↔ (m ≡ 2 ⋅ n)
interleave-left-args {n = n} = [↔]-intro (\{[≡]-intro → interleave-left{n = n}}) r where
  r : ⦃ _ : Injective(af) ⦄ → ∀{m n} → (interleave af bf m ≡ Either.Left(af(n))) → (m ≡ 2 ⋅ n)
  r {af = af} {m = 𝟎}{n = n} = congruence₁(2 ⋅_) ∘ injective(af) ∘ injective(Either.Left)
  r {af = af}{bf = bf} {m = 𝐒 (𝐒 m)}{n = 𝟎} p with interleave-values {af = af}{bf = bf}{n = 𝐒(𝐒 m)}
  ... | [∨]-introₗ v with () ← injective(af) (injective(Either.Left) (symmetry(_≡_) v 🝖 p))
  ... | [∨]-introᵣ v with () ← symmetry(_≡_) v 🝖 p
  r {af = af} {m = 𝐒 (𝐒 m)}{n = 𝐒 n} p = congruence₁(𝐒 ∘ 𝐒) (r ⦃ [∘]-injective {f = af} ⦄{m = m}{n = n} p)

interleave-right-args : ⦃ _ : Injective(bf) ⦄ → ∀{m n} → (interleave af bf m ≡ Either.Right(bf(n))) ↔ (m ≡ 𝐒(2 ⋅ n))
interleave-right-args {n = n} = [↔]-intro (\{[≡]-intro → interleave-right{n = n}}) r where
  r : ⦃ _ : Injective(bf) ⦄ → ∀{m n} → (interleave af bf m ≡ Either.Right(bf(n))) → (m ≡ 𝐒(2 ⋅ n))
  r {bf = bf} {m = 𝐒 𝟎}{n = n} = congruence₁(𝐒 ∘ (2 ⋅_)) ∘ injective(bf) ∘ injective(Either.Right)
  r {bf = bf}{af = af} {m = 𝐒 (𝐒 m)}{n = 𝟎} p with interleave-values {af = af}{bf = bf}{n = 𝐒(𝐒 m)}
  ... | [∨]-introₗ v with () ← symmetry(_≡_) v 🝖 p
  ... | [∨]-introᵣ v with () ← injective(bf) (injective(Either.Right) (symmetry(_≡_) v 🝖 p))
  r {bf = bf} {m = 𝐒 (𝐒 m)}{n = 𝐒 n} p = congruence₁(𝐒 ∘ 𝐒) (r ⦃ [∘]-injective {f = bf} ⦄{m = m}{n = n} p)

interleave-step-left : ⦃ _ : Injective(af) ⦄ → ∀{m n} → (interleave af bf m ≡ Either.Left(af(n))) ↔ (interleave af bf (𝐒(𝐒 m)) ≡ Either.Left(af(𝐒 n)))
interleave-step-left{af = iaf}{bf = ibf}{m = m}{n = n} = [↔]-intro (l{af = iaf}{bf = ibf}{m = m}{n = n}) (r{af = iaf}{bf = ibf}{m = m}{n = n}) where
  l : ⦃ _ : Injective(af) ⦄ → ∀{m n} → (interleave af bf m ≡ Either.Left(af(n))) ← (interleave af bf (𝐒(𝐒 m)) ≡ Either.Left(af(𝐒 n)))
  l {af = af}          {m = 𝟎}      {n}   = congruence₁(Either.Left) ∘ congruence₁(af) ∘ injective(𝐒) ∘ injective(af) ∘ injective(Either.Left)
  l {af = af}{bf = bf} {m = 𝐒 (𝐒 m)}{𝟎}   p with interleave-values {af = af}{bf = bf}{n = 𝐒(𝐒(𝐒(𝐒 m)))}
  ... | [∨]-introₗ v with () ← injective(af) (injective(Either.Left) (symmetry(_≡_) v 🝖 p))
  ... | [∨]-introᵣ v with () ← symmetry(_≡_) v 🝖 p
  l {af = af}          {m = 𝐒 (𝐒 m)}{𝐒 n} = l {af = af ∘ 𝐒} ⦃ [∘]-injective {f = af} ⦄ {m = m}{n}

  r : ⦃ _ : Injective(af) ⦄ → ∀{m n} → (interleave af bf m ≡ Either.Left(af(n))) → (interleave af bf (𝐒(𝐒 m)) ≡ Either.Left(af(𝐒 n)))
  r {af = af}          {m = 𝟎}      {n}   = congruence₁(Either.Left) ∘ congruence₁(af) ∘ congruence₁(𝐒) ∘ injective(af) ∘ injective(Either.Left)
  r {af = af}{bf = bf} {m = 𝐒(𝐒 m)} {𝟎}   p with interleave-values {af = af}{bf = bf}{n = 𝐒(𝐒 m)}
  ... | [∨]-introₗ v with () ← injective(af) (injective(Either.Left) (symmetry(_≡_) v 🝖 p))
  ... | [∨]-introᵣ v with () ← symmetry(_≡_) v 🝖 p
  r {af = af}          {m = 𝐒(𝐒 m)} {𝐒 n} = r {af = af ∘ 𝐒} ⦃ [∘]-injective {f = af} ⦄ {m = m}{n}


postulate interleave-injective-raw : ⦃ inj-af : Injective(af) ⦄ → ⦃ inj-bf : Injective(bf) ⦄ → Names.Injective(interleave af bf)
{-interleave-injective-raw {af = af} {bf = bf} {x = 𝟎}       {y = 𝟎}       fxfy = [≡]-intro
interleave-injective-raw {af = af} {bf = bf} {x = 𝟎}       {y = 𝐒 (𝐒 y)} fxfy = symmetry(_≡_) ([↔]-to-[→] (interleave-left-args {bf = bf}) (symmetry(_≡_) fxfy))
interleave-injective-raw {af = af} {bf = bf} {x = 𝐒 (𝐒 x)} {y = 𝟎}       fxfy = [↔]-to-[→] (interleave-left-args {bf = bf}) fxfy
interleave-injective-raw {af = af} {bf = bf} {x = 𝐒 𝟎} {y = 𝐒 𝟎} fxfy = [≡]-intro
interleave-injective-raw {af = af} {bf = bf} {x = 𝐒 𝟎} {y = 𝐒 (𝐒 y)} fxfy = symmetry(_≡_) ([↔]-to-[→] (interleave-right-args {bf = bf}{af = af}) (symmetry(_≡_) fxfy))
interleave-injective-raw {af = af} {bf = bf} {x = 𝐒 (𝐒 x)} {y = 𝐒 𝟎} fxfy = [↔]-to-[→] (interleave-right-args {bf = bf}{af = af}) fxfy
interleave-injective-raw {af = af} {bf = bf} {x = 𝐒 (𝐒 x)} {y = 𝐒 (𝐒 y)} fxfy with interleave-values {af = af ∘ 𝐒}{bf = bf ∘ 𝐒}{n = x} | interleave-values {af = af ∘ 𝐒}{bf = bf ∘ 𝐒}{n = y}
... | [∨]-introₗ p | [∨]-introₗ q = {!congruence₁(𝐒) (injective(af) (injective(Either.Left) (symmetry(_≡_) p 🝖 fxfy 🝖 q)))!} -- TODO: interleave-left and a proof of the division algorihm would work here instead of using interleave-values. Or alternatively, use this, multiply by 2, prove the divisibilities for both cases so that each case have division as inverse of multiplication
... | [∨]-introₗ p | [∨]-introᵣ q = {!!}
... | [∨]-introᵣ p | [∨]-introₗ q = {!!}
... | [∨]-introᵣ p | [∨]-introᵣ q = {!congruence₁(𝐒) (injective(bf) (injective(Either.Right) (symmetry(_≡_) p 🝖 fxfy 🝖 q)))!}
-}

instance
  interleave-injective : ⦃ inj-af : Injective(af) ⦄ → ⦃ inj-bf : Injective(bf) ⦄ → Injective(interleave af bf)
  interleave-injective = intro interleave-injective-raw

instance
  interleave-surjective : ⦃ surj-af : Surjective(af) ⦄ → ⦃ surj-bf : Surjective(bf) ⦄ → Surjective(interleave af bf)
  Surjective.proof (interleave-surjective {af = af}{bf = bf}) {[∨]-introₗ y} with surjective(af){y}
  ... | [∃]-intro n ⦃ [≡]-intro ⦄ = [∃]-intro(2 ⋅ n) ⦃ interleave-left{n = n} ⦄
  Surjective.proof (interleave-surjective {af = af}{bf = bf}) {[∨]-introᵣ y} with surjective(bf){y}
  ... | [∃]-intro n ⦃ [≡]-intro ⦄ = [∃]-intro(𝐒(2 ⋅ n)) ⦃ interleave-right{n = n} ⦄

instance
  interleave-bijective : ⦃ bij-af : Bijective(af) ⦄ → ⦃ bij-bf : Bijective(bf) ⦄ → Bijective(interleave af bf)
  interleave-bijective {af = af}{bf = bf} = injective-surjective-to-bijective(interleave af bf) where
    instance
      inj-af : Injective(af)
      inj-af = bijective-to-injective af
    instance
      inj-bf : Injective(bf)
      inj-bf = bijective-to-injective bf
    instance
      surj-af : Surjective(af)
      surj-af = bijective-to-surjective af
    instance
      surj-bf : Surjective(bf)
      surj-bf = bijective-to-surjective bf
