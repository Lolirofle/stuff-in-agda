module Numeral.Finite.Oper.Bounded.Proofs.fromℕ where

open import Data
open import Logic.Propositional
open import Numeral.Natural as ℕ
import      Numeral.Natural.Oper as ℕ
import      Numeral.Natural.Function as ℕ renaming (min to minf)
-- open import Numeral.Natural.Proofs
import      Numeral.Natural.Relation as ℕ
import      Numeral.Natural.Relation.Order as ℕ
import      Numeral.Natural.Relation.Order.Proofs as ℕ
open import Numeral.Finite as 𝕟
-- open import Numeral.Finite.Bound
-- open import Numeral.Finite.Bound.Proofs
-- open import Numeral.Finite.Oper using (module Exact)
-- open import Numeral.Finite.Oper.Wrapping renaming (𝐒 to [𝐒] ; 𝐏 to [𝐏])
open import Numeral.Finite.Oper.Bounded as Bounded
-- open import Numeral.Finite.Proofs
-- open import Numeral.Finite.Recursion
open import Numeral.Finite.Relation.Order
open import Numeral.Finite.Relation.Order.Proofs
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Type.Identity
open import Type.Identity.Proofs

private variable b b₁ b₂ N A B : ℕ
private variable n x y z x₁ x₂ y₁ y₂ : 𝕟(N)

fromℕ-of-𝟎 : .⦃ pos : ℕ.Positive(b₁) ⦄ → (Bounded.fromℕ{b₁}(𝟎) ≡ 𝟎 {b₂})
fromℕ-of-𝟎 {ℕ.𝐒 𝟎}       = <>
fromℕ-of-𝟎 {ℕ.𝐒 (ℕ.𝐒 _)} = <>

-- TODO: There is also the case where one side overflows and the bound is equal to the successor of the other side.
fromℕ-function : .⦃ pos₁ : ℕ.Positive(b₁) ⦄ → .⦃ pos₂ : ℕ.Positive(b₂) ⦄ → (A ℕ.< b₁) → (B ℕ.< b₂) → Id A B →(Bounded.fromℕ{b₁}(A) ≡ Bounded.fromℕ{b₂}(B))
fromℕ-function {ℕ.𝐒 𝟎}       {ℕ.𝐒 𝟎}       {𝟎}     (ℕ.succ ℕ.min)      (ℕ.succ ℕ.min)      intro = <>
fromℕ-function {ℕ.𝐒(ℕ.𝐒 b₁)} {ℕ.𝐒 𝟎}       {𝟎}     (ℕ.succ ℕ.min)      (ℕ.succ ℕ.min)      intro = <>
fromℕ-function {ℕ.𝐒 𝟎}       {ℕ.𝐒(ℕ.𝐒 b₂)} {𝟎}     (ℕ.succ ℕ.min)      (ℕ.succ ℕ.min)      intro = <>
fromℕ-function {ℕ.𝐒(ℕ.𝐒 b₁)} {ℕ.𝐒(ℕ.𝐒 b₂)} {𝟎}     (ℕ.succ ℕ.min)      (ℕ.succ ℕ.min)      intro = <>
fromℕ-function {ℕ.𝐒(ℕ.𝐒 b₁)} {ℕ.𝐒(ℕ.𝐒 b₂)} {ℕ.𝐒 N} (ℕ.succ(ℕ.succ bl)) (ℕ.succ(ℕ.succ br)) intro = fromℕ-function {ℕ.𝐒 b₁} {ℕ.𝐒 b₂} {N} (ℕ.succ bl) (ℕ.succ br) intro

fromℕ-function-by-min : .⦃ pos₁ : ℕ.Positive(b₁) ⦄ → .⦃ pos₂ : ℕ.Positive(b₂) ⦄ → Id (ℕ.minf A (ℕ.𝐏(b₁))) (ℕ.minf B (ℕ.𝐏(b₂))) → (Bounded.fromℕ{b₁}(A) ≡ Bounded.fromℕ{b₂}(B))


fromℕ-function-overflowₗ : .⦃ pos₁ : ℕ.Positive(b₁) ⦄ → .⦃ pos₂ : ℕ.Positive(b₂) ⦄ → (A ℕ.≥ b₁) → (B ℕ.< b₂) → Id (ℕ.𝐏(b₁)) B → (Bounded.fromℕ{b₁}(A) ≡ Bounded.fromℕ{b₂}(B))
fromℕ-function-overflowₗ {ℕ.𝐒 𝟎}       {ℕ.𝐒 𝟎}       {ℕ.𝐒 A}      {𝟎}     _ _                    _ = <>
fromℕ-function-overflowₗ {ℕ.𝐒 𝟎}       {ℕ.𝐒(ℕ.𝐒 b₂)} {ℕ.𝐒 A}      {𝟎}     _ _                    _ = <>
fromℕ-function-overflowₗ {ℕ.𝐒 (ℕ.𝐒 𝟎)} {ℕ.𝐒 𝟎} {ℕ.𝐒 (ℕ.𝐒 A)} {ℕ.𝐒 .0} (ℕ.succ (ℕ.succ ord)) (ℕ.succ ()) intro
fromℕ-function-overflowₗ {ℕ.𝐒 (ℕ.𝐒 𝟎)} {ℕ.𝐒 (ℕ.𝐒 b₂)} {ℕ.𝐒 (ℕ.𝐒 A)} {ℕ.𝐒 .0} (ℕ.succ (ℕ.succ ord)) p intro = {!!}
fromℕ-function-overflowₗ {ℕ.𝐒 (ℕ.𝐒 (ℕ.𝐒 b₁))} {ℕ.𝐒 b₂} {ℕ.𝐒 (ℕ.𝐒 A)} {ℕ.𝐒 .(ℕ.𝐒 b₁)} (ℕ.succ (ℕ.succ ord)) p intro = {!!}

fromℕ-of-𝐒 : .⦃ pos₁ : ℕ.Positive(b₁) ⦄ → .⦃ pos₂ : ℕ.Positive(b₂) ⦄ → (Bounded.fromℕ{b₁}(ℕ.𝐒(N)) ≡ 𝕟.𝐒(Bounded.fromℕ{b₂}(N)))-- (ℕ.𝐒(N) ℕ.< b) →
fromℕ-of-𝐒 {ℕ.𝐒 b₁} {ℕ.𝐒 b₂} {𝟎} = {![≡]-reflexivity-raw {}!}
fromℕ-of-𝐒 {ℕ.𝐒 b₁} {ℕ.𝐒 b₂} {ℕ.𝐒 N} = {!!}
-- fromℕ-of-𝐒 {ℕ.𝐒 𝟎}       {N} (ℕ.succ ())
-- fromℕ-of-𝐒 {ℕ.𝐒 (ℕ.𝐒 b)} {N} (ℕ.succ ord) = {!reflexivity(_≡_) {x = 𝕟.𝐒(Bounded.fromℕ(N))}!}
-- fromℕ-of-𝐒 {ℕ.𝐒 (ℕ.𝐒 𝟎)}       {𝟎} (ℕ.succ (ℕ.succ ℕ.min)) = <>
-- fromℕ-of-𝐒 {ℕ.𝐒 (ℕ.𝐒 (ℕ.𝐒 b))} {𝟎} (ℕ.succ (ℕ.succ ℕ.min)) = <>
-- fromℕ-of-𝐒 {ℕ.𝐒 (ℕ.𝐒 (ℕ.𝐒 b))} {ℕ.𝐒 N} (ℕ.succ (ℕ.succ (ℕ.succ ord))) = {!!}

fromℕ-toℕ-inverse : .⦃ pos : ℕ.Positive(b) ⦄ → (toℕ(n) ℕ.< b) → (Bounded.fromℕ{b}(toℕ(n)) ≡ n)
fromℕ-toℕ-inverse {b = b} {n = 𝟎} (ℕ.succ ord) = fromℕ-of-𝟎 {b₁ = b}
fromℕ-toℕ-inverse {n = 𝕟.𝐒 n} (ℕ.succ ord) = {!!}

toℕ-fromℕ-inverse : .⦃ pos : ℕ.Positive(b) ⦄ → (N ℕ.< b) → Id (toℕ(Bounded.fromℕ{b}(N))) N
toℕ-fromℕ-inverse {ℕ.𝐒 𝟎}       {N = 𝟎}     _           = intro
toℕ-fromℕ-inverse {ℕ.𝐒 (ℕ.𝐒 b)} {N = 𝟎}     _           = intro
toℕ-fromℕ-inverse {ℕ.𝐒 𝟎}       {N = ℕ.𝐒 N} (ℕ.succ ())
toℕ-fromℕ-inverse {ℕ.𝐒 (ℕ.𝐒 b)} {N = ℕ.𝐒 N} (ℕ.succ (ℕ.succ p)) = congruence₁ ⦃ _ ⦄ ⦃ _ ⦄ (ℕ.𝐒) ⦃ Id-function ⦄ (toℕ-fromℕ-inverse {ℕ.𝐒 b} {N = N} (ℕ.succ p))
