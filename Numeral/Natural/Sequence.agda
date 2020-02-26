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
open import Relator.Equals.Proofs.Equivalence
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
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
pairIndexing 𝟎     (𝐒 b) = 𝐒(pairIndexing b 𝟎)
pairIndexing (𝐒 a) b     = 𝐒(pairIndexing a (𝐒 b))



private variable af : ℕ → A
private variable bf : ℕ → B

{-# TERMINATING #-}
pairIndexing-injective-raw : ∀{a₁ b₁ a₂ b₂} → (pairIndexing a₁ b₁ ≡ pairIndexing a₂ b₂) → ((a₁ ≡ a₂) ∧ (b₁ ≡ b₂))
pairIndexing-injective-raw {𝟎} {𝟎} {𝟎} {𝟎} p = [∧]-intro [≡]-intro [≡]-intro
pairIndexing-injective-raw {𝟎} {𝐒 b₁} {𝟎} {𝐒 b₂} p = [∧]-intro [≡]-intro ([≡]-with(𝐒) ([∧]-elimₗ(pairIndexing-injective-raw (injective(𝐒) p))))
pairIndexing-injective-raw {𝟎} {𝐒 b₁} {𝐒 a₂} {b₂} p with [∧]-intro _ () ← pairIndexing-injective-raw {b₁} {𝟎} {a₂} {𝐒 b₂} (injective(𝐒) p)
pairIndexing-injective-raw {𝐒 a₁} {b₁} {𝟎} {𝐒 b₂} p with [∧]-intro _ () ← pairIndexing-injective-raw {a₁} {𝐒 b₁} {b₂} {𝟎} (injective(𝐒) p)
pairIndexing-injective-raw {𝐒 a₁} {b₁} {𝐒 a₂} {b₂} p = Tuple.map ([≡]-with(𝐒)) (injective(𝐒)) (pairIndexing-injective-raw {a₁} {𝐒 b₁} {a₂} {𝐒 b₂} (injective(𝐒) p))

pairIndexing-injective : Injective(Tuple.uncurry pairIndexing)
Injective.proof pairIndexing-injective {a₁ , b₁} {a₂ , b₂} p = Tuple.uncurry Tuple-equality (pairIndexing-injective-raw p)



{-
interleave-left : ∀{n} → (interleave af bf (2 ⋅ n) ≡ Either.Left(af(n)))
interleave-left {n = 𝟎}   = [≡]-intro
interleave-left {n = 𝐒 n} = interleave-left {n = n}
{-# REWRITE interleave-left #-}

interleave-right : ∀{n} → (interleave af bf (𝐒(2 ⋅ n)) ≡ Either.Right(bf(n)))
interleave-right {n = 𝟎}   = [≡]-intro
interleave-right {n = 𝐒 n} = interleave-right {n = n}
{-# REWRITE interleave-right #-}

interleave-values : ∀{n} → (interleave af bf n ≡ Either.Left(af(n ⌊/⌋ 2))) ∨ (interleave af bf n ≡ Either.Right(bf(n ⌊/⌋ 2)))
interleave-values                    {n = 𝟎}      = [∨]-introₗ [≡]-intro
interleave-values                    {n = 𝐒 𝟎}    = [∨]-introᵣ [≡]-intro
interleave-values {af = af}{bf = bf} {n = 𝐒(𝐒 n)} = interleave-values {af = af ∘ 𝐒}{bf = bf ∘ 𝐒} {n = n}

interleave-left-args : ⦃ _ : Injective(af) ⦄ → ∀{m n} → (interleave af bf m ≡ Either.Left(af(n))) ↔ (m ≡ 2 ⋅ n)
interleave-left-args {n = n} = [↔]-intro (\{[≡]-intro → [≡]-intro}) r where
  r : ⦃ _ : Injective(af) ⦄ → ∀{m n} → (interleave af bf m ≡ Either.Left(af(n))) → (m ≡ 2 ⋅ n)
  r {af = af} {m = 𝟎}{n = n} = [≡]-with(2 ⋅_) ∘ injective(af) ∘ injective(Either.Left)
  r {af = af}{bf = bf} {m = 𝐒 (𝐒 m)}{n = 𝟎} p with interleave-values {af = af}{bf = bf}{n = 𝐒(𝐒 m)}
  ... | [∨]-introₗ v with () ← injective(af) (injective(Either.Left) (symmetry(_≡_) v 🝖 p))
  ... | [∨]-introᵣ v with () ← symmetry(_≡_) v 🝖 p
  r {af = af} {m = 𝐒 (𝐒 m)}{n = 𝐒 n} p = [≡]-with(𝐒 ∘ 𝐒) (r ⦃ [∘]-injective {f = af} ⦄{m = m}{n = n} p)

interleave-right-args : ⦃ _ : Injective(bf) ⦄ → ∀{m n} → (interleave af bf m ≡ Either.Right(bf(n))) ↔ (m ≡ 𝐒(2 ⋅ n))
interleave-right-args {n = n} = [↔]-intro (\{[≡]-intro → [≡]-intro}) r where
  r : ⦃ _ : Injective(bf) ⦄ → ∀{m n} → (interleave af bf m ≡ Either.Right(bf(n))) → (m ≡ 𝐒(2 ⋅ n))
  r {bf = bf} {m = 𝐒 𝟎}{n = n} = [≡]-with(𝐒 ∘ (2 ⋅_)) ∘ injective(bf) ∘ injective(Either.Right)
  r {bf = bf}{af = af} {m = 𝐒 (𝐒 m)}{n = 𝟎} p with interleave-values {af = af}{bf = bf}{n = 𝐒(𝐒 m)}
  ... | [∨]-introₗ v with () ← symmetry(_≡_) v 🝖 p
  ... | [∨]-introᵣ v with () ← injective(bf) (injective(Either.Right) (symmetry(_≡_) v 🝖 p))
  r {bf = bf} {m = 𝐒 (𝐒 m)}{n = 𝐒 n} p = [≡]-with(𝐒 ∘ 𝐒) (r ⦃ [∘]-injective {f = bf} ⦄{m = m}{n = n} p)

interleave-step-left : ⦃ _ : Injective(af) ⦄ → ∀{m n} → (interleave af bf m ≡ Either.Left(af(n))) ↔ (interleave af bf (𝐒(𝐒 m)) ≡ Either.Left(af(𝐒 n)))
interleave-step-left{af = iaf}{bf = ibf}{m = m}{n = n} = [↔]-intro (l{af = iaf}{bf = ibf}{m = m}{n = n}) (r{af = iaf}{bf = ibf}{m = m}{n = n}) where
  l : ⦃ _ : Injective(af) ⦄ → ∀{m n} → (interleave af bf m ≡ Either.Left(af(n))) ← (interleave af bf (𝐒(𝐒 m)) ≡ Either.Left(af(𝐒 n)))
  l {af = af}          {m = 𝟎}      {n}   = [≡]-with(Either.Left) ∘ [≡]-with(af) ∘ injective(𝐒) ∘ injective(af) ∘ injective(Either.Left)
  l {af = af}{bf = bf} {m = 𝐒 (𝐒 m)}{𝟎}   p with interleave-values {af = af}{bf = bf}{n = 𝐒(𝐒(𝐒(𝐒 m)))}
  ... | [∨]-introₗ v with () ← injective(af) (injective(Either.Left) (symmetry(_≡_) v 🝖 p))
  ... | [∨]-introᵣ v with () ← symmetry(_≡_) v 🝖 p
  l {af = af}          {m = 𝐒 (𝐒 m)}{𝐒 n} = l {af = af ∘ 𝐒} ⦃ [∘]-injective {f = af} ⦄ {m = m}{n}

  r : ⦃ _ : Injective(af) ⦄ → ∀{m n} → (interleave af bf m ≡ Either.Left(af(n))) → (interleave af bf (𝐒(𝐒 m)) ≡ Either.Left(af(𝐒 n)))
  r {af = af}          {m = 𝟎}      {n}   = [≡]-with(Either.Left) ∘ [≡]-with(af) ∘ [≡]-with(𝐒) ∘ injective(af) ∘ injective(Either.Left)
  r {af = af}{bf = bf} {m = 𝐒(𝐒 m)} {𝟎}   p with interleave-values {af = af}{bf = bf}{n = 𝐒(𝐒 m)}
  ... | [∨]-introₗ v with () ← injective(af) (injective(Either.Left) (symmetry(_≡_) v 🝖 p))
  ... | [∨]-introᵣ v with () ← symmetry(_≡_) v 🝖 p
  r {af = af}          {m = 𝐒(𝐒 m)} {𝐒 n} = r {af = af ∘ 𝐒} ⦃ [∘]-injective {f = af} ⦄ {m = m}{n}

instance
  interleave-injective : ⦃ Injective(af) ⦄ → ⦃ Injective(bf) ⦄ → Injective(interleave af bf)
  Injective.proof interleave-injective                      {𝟎}     {𝟎}      fxfy = [≡]-intro
  Injective.proof interleave-injective                      {𝐒 𝟎}   {𝐒 𝟎}    fxfy = [≡]-intro
  Injective.proof (interleave-injective {af = af}{bf = bf}) {𝟎}     {𝐒(𝐒 y)} fxfy with interleave-values{af = af}{bf = bf} {n = 𝐒(𝐒 y)}
  ... | [∨]-introₗ p with () ← injective(af) (injective(Either.Left) (fxfy 🝖 p))
  ... | [∨]-introᵣ p with () ← fxfy 🝖 p
  Injective.proof (interleave-injective {af = af}{bf = bf}) {𝐒(𝐒 x)}{𝟎}      fxfy with interleave-values{af = af}{bf = bf} {n = 𝐒(𝐒 x)}
  ... | [∨]-introₗ p with () ← injective(af) (injective(Either.Left) (symmetry(_≡_) fxfy 🝖 p))
  ... | [∨]-introᵣ p with () ← symmetry(_≡_) fxfy 🝖 p
  Injective.proof (interleave-injective {af = af}{bf = bf}) {𝐒 𝟎}   {𝐒(𝐒 y)} fxfy with interleave-values{af = af}{bf = bf} {n = 𝐒(𝐒 y)}
  ... | [∨]-introₗ p with () ← fxfy 🝖 p
  ... | [∨]-introᵣ p with () ← injective(bf) (injective(Either.Right) (fxfy 🝖 p))
  Injective.proof (interleave-injective {af = af}{bf = bf}) {𝐒(𝐒 x)}{𝐒 𝟎}    fxfy with interleave-values{af = af}{bf = bf} {n = 𝐒(𝐒 x)}
  ... | [∨]-introₗ p with () ← symmetry(_≡_) fxfy 🝖 p
  ... | [∨]-introᵣ p with () ← injective(bf) (injective(Either.Right) (symmetry(_≡_) fxfy 🝖 p))
  Injective.proof (interleave-injective {af = af}{bf = bf}) {𝐒(𝐒 x)}{𝐒(𝐒 y)} fxfy = [≡]-with(𝐒 ∘ 𝐒) (Injective.proof (interleave-injective {af = af}{bf = bf}) {x} {y} {!!})

instance
  interleave-surjective : ⦃ Surjective(af) ⦄ → ⦃ Surjective(bf) ⦄ → Surjective(interleave af bf)
  Surjective.proof (interleave-surjective {af = af}{bf = bf}) {[∨]-introₗ y} with surjective(af){y}
  ... | [∃]-intro n ⦃ [≡]-intro ⦄ = [∃]-intro(2 ⋅ n) ⦃ [≡]-intro ⦄
  Surjective.proof (interleave-surjective {af = af}{bf = bf}) {[∨]-introᵣ y} with surjective(bf){y}
  ... | [∃]-intro n ⦃ [≡]-intro ⦄ = [∃]-intro(𝐒(2 ⋅ n)) ⦃ [≡]-intro ⦄
-}
