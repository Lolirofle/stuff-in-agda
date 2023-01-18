module Numeral.Finite.Oper.Proofs where

open import Data
import      Data.Option.Functions as Option
open import Data.Option.Proofs
import      Data.Option.Relation as Option
open import Functional
open import Logic.Predicate
open import Logic.Propositional
open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Finite.Functions
open import Numeral.Finite.Oper
import      Numeral.Finite.Oper.Bounded as Bounded
open import Numeral.Finite.Oper.Bounded.Proofs.𝐏
open import Numeral.Finite.Proofs
import      Numeral.Finite.Relation.Order as 𝕟
open import Numeral.Natural
import      Numeral.Natural.Relation as ℕ
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Function.Domain
import      Structure.Function.Names as Names
open import Structure.Relator.Properties
open import Syntax.Transitivity

module _ where
  open import Numeral.Finite.Proofs
  open import Numeral.Finite.Relation.Order.Proofs

  shift𝐏ByRepeat-def1 : ∀{n} ⦃ pos : ℕ.Positive(n) ⦄ {c : 𝕟(n)}{x : 𝕟(𝐒(n))} → (c 𝕟.< x) → (shift𝐏ByRepeat c x ≡ Bounded.𝐏(x))
  shift𝐏ByRepeat-def1 {.(𝐒 _)}     {c = 𝟎 {n}}     {𝐒 x}        cx = symmetry(_≡_) ([↔]-to-[←] [≡][≡?]-equivalence (bounded-𝐏-𝐒-inverses {N₂ = 𝐒 n} ([≤]-maximum₌ {a = x})))
  shift𝐏ByRepeat-def1 {.(𝐒 (𝐒 n))} {c = 𝐒 {𝐒 n} c} {𝐒(x@(𝐒 _))} cx =
    shift𝐏ByRepeat(𝐒(c)) (𝐒(x)) 🝖[ _≡_ ]-[ congruence₁(𝐒) (shift𝐏ByRepeat-def1 {c = c} {x} cx) ]
    𝐒(Bounded.𝐏(x))          🝖[ _≡_ ]-[ [↔]-to-[←] [≡][≡?]-equivalence (bounded-𝐏-𝐒-preserving {Nₗ = 𝐒(𝐒(n))}{Nᵣ = 𝐒(n)}{x = x} ([≤]-maximum₌ {a = x}) ([≤]-maximum₌ {a = x})) ]
    Bounded.𝐏(𝐒(x))          🝖-end

  shift𝐏ByRepeat-def1 {.(𝐒 (𝐒 n))} {c = 𝐒 {𝐒 n} 𝟎} {𝐒 𝟎} ()
  shift𝐏ByRepeat-def1 {.(𝐒 (𝐒 n))} {c = 𝐒 {𝐒 n} (𝐒 c)} {𝐒 𝟎} ()

  shift𝐏ByRepeat-def2 : ∀{n}{c : 𝕟(n)}{x : 𝕟(𝐒(n))} → (c 𝕟.≥ x) → (shift𝐏ByRepeat c x 𝕟.≡ x)
  shift𝐏ByRepeat-def2 {𝐒 n} {c = 𝟎} {𝟎} cx = <>
  shift𝐏ByRepeat-def2 {𝐒 n} {c = 𝐒 c} {𝟎} cx = <>
  shift𝐏ByRepeat-def2 {𝐒 (𝐒 n)} {c = 𝐒 c} {𝐒 x} cx = shift𝐏ByRepeat-def2 {𝐒 n} {c = c} {x} cx

shift𝐏ByRepeat-surjective : ∀{n}{c : 𝕟(n)} → Surjective(shift𝐏ByRepeat c)
shift𝐏ByRepeat-surjective = intro p where
  p : ∀{n}{c : 𝕟(n)} → Names.Surjective(shift𝐏ByRepeat c)
  p{𝐒 n}{c}  {𝟎}   = [∃]-intro 𝟎
  p{𝐒 n}{𝟎}  {𝐒 y} = [∃]-intro (𝐒(𝐒(y)))
  p{𝐒 n}{𝐒 c}{𝐒 y} =
    let [∃]-intro prev ⦃ eq ⦄ = p{n}{c}{y}
    in [∃]-intro (𝐒(prev)) ⦃ congruence₁(𝐒) eq ⦄

shift𝐏BySkip-injective : ∀{n}{c : 𝕟(𝐒(n))}{x y} .⦃ cx : c 𝕟.≢ x ⦄ .⦃ cy : c 𝕟.≢ y ⦄ → (shift𝐏BySkip c x ≡ shift𝐏BySkip c y) → (x ≡ y)
shift𝐏BySkip-injective {𝐒 n} {𝟎}   {𝐒 x} {𝐒 y} = congruence₁(𝐒)
shift𝐏BySkip-injective {𝐒 n} {𝐒 c} {𝟎}   {𝟎}   = const [≡]-intro
shift𝐏BySkip-injective {𝐒 n} {𝐒 c} {𝐒 x} {𝐒 y} = congruence₁(𝐒) ∘ shift𝐏BySkip-injective {n} {c} {x} {y} ∘ injective(𝐒)

shift𝐏ByRepeatRestrict-almost-injective : ∀{n} ⦃ pos : ℕ.Positive(n) ⦄ {c x y : 𝕟(𝐒 n)} .⦃ cx : c 𝕟.≢ x ⦄ .⦃ cy : c 𝕟.≢ y ⦄ → (shift𝐏ByRepeatRestrict c x ≡ shift𝐏ByRepeatRestrict c y) → (x ≡ y)
shift𝐏ByRepeatRestrict-almost-injective {𝐒 𝟎}   {𝟎}  {𝐒 𝟎}{𝐒 𝟎} _ = [≡]-intro
shift𝐏ByRepeatRestrict-almost-injective {𝐒 𝟎}   {𝐒 c}{𝟎}  {𝟎}   _ = [≡]-intro
shift𝐏ByRepeatRestrict-almost-injective {𝐒 𝟎}   {𝐒 𝟎}{𝟎}  {𝐒 𝟎} ⦃ _ ⦄ ⦃  ⦄
shift𝐏ByRepeatRestrict-almost-injective {𝐒 𝟎}   {𝐒 c}{𝐒 𝟎}{𝐒 𝟎} _ = [≡]-intro
shift𝐏ByRepeatRestrict-almost-injective {𝐒 𝟎}   {𝐒 𝟎}{𝐒 𝟎}{𝟎}   ⦃ ⦄   ⦃ _ ⦄
shift𝐏ByRepeatRestrict-almost-injective {𝐒(𝐒 n)}{𝐒 c}{𝟎}  {𝟎}     = const [≡]-intro
shift𝐏ByRepeatRestrict-almost-injective {𝐒(𝐒 n)}{𝟎}  {𝐒 x}{𝐒 y}   = congruence₁(𝐒)
shift𝐏ByRepeatRestrict-almost-injective {𝐒(𝐒 n)}{𝐒 c}{𝐒 x}{𝐒 y}   = congruence₁(𝐒) ∘ shift𝐏ByRepeatRestrict-almost-injective {𝐒 n}{c}{x}{y} ∘ injective(𝐒)

shift𝐏ByRepeat-shift𝐏BySkip-eq : ∀{n}{c₁ c₂}{x : 𝕟(𝐒(n))} ⦃ nc₂x : c₂ 𝕟.≢ x ⦄ → (c₁ 𝕟.≡ c₂) → (shift𝐏ByRepeat c₁ x ≡ shift𝐏BySkip c₂ x)
shift𝐏ByRepeat-shift𝐏BySkip-eq {c₁ = 𝟎}   {𝟎}   {𝐒 x} c₁c₂ = [≡]-intro
shift𝐏ByRepeat-shift𝐏BySkip-eq {c₁ = 𝐒 c₁}{𝐒 c₂}{𝟎}   c₁c₂ = [≡]-intro
shift𝐏ByRepeat-shift𝐏BySkip-eq {c₁ = 𝐒 c₁}{𝐒 c₂}{𝐒 x} c₁c₂ = congruence₁(𝐒) (shift𝐏ByRepeat-shift𝐏BySkip-eq {c₁ = c₁}{c₂}{x} c₁c₂)

shift𝐏ByRepeat-shift𝐏ByRepeatRestrict-eq : ∀{m n} ⦃ pos : ℕ.Positive(n) ⦄ {c₁}{c₂ : 𝕟(m)}{x : 𝕟(𝐒(n))} → (c₁ 𝕟.≡ c₂) → (shift𝐏ByRepeat c₁ x ≡ shift𝐏ByRepeatRestrict c₂ x)
shift𝐏ByRepeat-shift𝐏ByRepeatRestrict-eq {𝐒 _}{𝐒 𝟎}   {𝟎}    {𝟎}   {𝟎}   c₁c₂ = [≡]-intro
shift𝐏ByRepeat-shift𝐏ByRepeatRestrict-eq {𝐒 _}{𝐒 𝟎}   {𝟎}    {𝟎}   {𝐒 𝟎} c₁c₂ = [≡]-intro
shift𝐏ByRepeat-shift𝐏ByRepeatRestrict-eq {𝐒 _}{𝐒(𝐒 n)}{𝟎}    {𝟎}   {𝟎}   c₁c₂ = [≡]-intro
shift𝐏ByRepeat-shift𝐏ByRepeatRestrict-eq {𝐒 _}{𝐒(𝐒 n)}{𝟎}    {𝟎}   {𝐒 x} c₁c₂ = [≡]-intro
shift𝐏ByRepeat-shift𝐏ByRepeatRestrict-eq {𝐒 _}{𝐒(𝐒 n)}{𝐒 c₁} {𝐒 c₂}{𝟎}   c₁c₂ = [≡]-intro
shift𝐏ByRepeat-shift𝐏ByRepeatRestrict-eq {𝐒 _}{𝐒(𝐒 n)}{𝐒 c₁} {𝐒 c₂}{𝐒 x} c₁c₂ = congruence₁(𝐒) (shift𝐏ByRepeat-shift𝐏ByRepeatRestrict-eq {_}{𝐒 n}{c₁}{c₂}{x} c₁c₂)

shift𝐏-is-none : ∀{C X}{c : 𝕟(C)}{x : 𝕟₌(X)} → (x 𝕟.≡ min c (maximum{𝐒(X)})) → Option.IsNone(Optional.shift𝐏 c x)
shift𝐏-is-none {X = 𝟎}  {c = _}  {x = _}   cx = <>
shift𝐏-is-none {X = 𝐒 X}{c = 𝟎}  {x = 𝟎}   cx = <>
shift𝐏-is-none {X = 𝐒 X}{c = 𝐒 c}{x = 𝐒 x} cx = map-is-none ⦃ shift𝐏-is-none {X = X}{c = c}{x = x} cx ⦄

shift𝐏-is-some : ∀{C X} {c : 𝕟(C)}{x : 𝕟₌(X)} → (x 𝕟.≢ min c (maximum{𝐒(X)})) → Option.IsSome(Optional.shift𝐏 c x)
shift𝐏-is-some {X = 𝐒 X}{𝟎}  {𝟎}   ()
shift𝐏-is-some {X = 𝐒 X}{𝟎}  {𝐒 x} cx = <>
shift𝐏-is-some {X = 𝐒 X}{𝐒 c}{𝟎}   cx = <>
shift𝐏-is-some {X = 𝐒 X}{𝐒 c}{𝐒 x} cx = map-is-some ⦃ some = shift𝐏-is-some {X = X} {c}{x} cx ⦄

shift𝐏-is-none-simple : ∀{X}{c x : 𝕟₌(X)} → (x 𝕟.≡ c) → Option.IsNone(Optional.shift𝐏 c x)
shift𝐏-is-none-simple {X = 𝟎}  {c = _}  {x = _}   cx = <>
shift𝐏-is-none-simple {X = 𝐒 X}{c = 𝟎}  {x = 𝟎}   cx = <>
shift𝐏-is-none-simple {X = 𝐒 X}{c = 𝐒 c}{x = 𝐒 x} cx = map-is-none ⦃ shift𝐏-is-none-simple {X = X}{c = c}{x = x} cx ⦄

shift𝐏-is-some-simple : ∀{X} {c x : 𝕟₌(X)} → (x 𝕟.≢ c) → Option.IsSome(Optional.shift𝐏 c x)
shift𝐏-is-some-simple {X = 𝐒 X}{𝟎}  {𝟎}   ()
shift𝐏-is-some-simple {X = 𝐒 X}{𝟎}  {𝐒 x} cx = <>
shift𝐏-is-some-simple {X = 𝐒 X}{𝐒 c}{𝟎}   cx = <>
shift𝐏-is-some-simple {X = 𝐒 X}{𝐒 c}{𝐒 x} cx = map-is-some ⦃ some = shift𝐏-is-some-simple {X = X} {c}{x} cx ⦄

module _ where
  import      Numeral.Finite.Relation as 𝕟
  import      Numeral.Finite.Relation.Order.Proofs as 𝕟
  import      Numeral.Natural.Relation.Order.Proofs as ℕ

  shift𝐏-some-value-lt : ∀{C X} {c : 𝕟(C)}{x : 𝕟₌(X)} → (cx : x 𝕟.< min c (maximum{𝐒(X)})) → (Option.extract(Optional.shift𝐏 c x) ⦃ shift𝐏-is-some (sub₂(𝕟._<_)(𝕟._≢_) {x} cx) ⦄ 𝕟.≡ x)
  shift𝐏-some-value-lt {X = 𝟎}   {𝟎}   {𝟎} ()
  shift𝐏-some-value-lt {X = 𝐒 X} {𝟎}   {x} cx with () ← 𝕟.[<]-minimumᵣ{a = x} cx
  shift𝐏-some-value-lt {X = 𝐒 X} {𝐒 c} {𝟎} cx = <>
  shift𝐏-some-value-lt {X = 𝐒 X} {𝐒 c} {𝐒 x} cx
    rewrite extract-map ⦃ [≡]-equiv ⦄ {f = 𝕟.𝐒}{o = Optional.shift𝐏 c x} ⦃ shift𝐏-is-some (sub₂(𝕟._<_)(𝕟._≢_) {x} cx) ⦄
    = shift𝐏-some-value-lt {X = X} {c} {x} cx

  shift𝐏-some-value-gt : ∀{C X} {c : 𝕟(C)}{x : 𝕟₌(X)} → (cx : x 𝕟.> min c (maximum{𝐒(X)})) → (Option.extract(Optional.shift𝐏 c x) ⦃ shift𝐏-is-some (sub₂(𝕟._>_)(𝕟._≢_) {x} cx) ⦄ 𝕟.≡ Bounded.𝐏{𝐒 X}{𝐒 X}(x))
  shift𝐏-some-value-gt {X = 𝐒 X}{𝟎}  {𝟎}   ()
  shift𝐏-some-value-gt {X = 𝐒 X}{𝐒 c}{𝟎}   ()
  shift𝐏-some-value-gt {X = 𝐒 X}{𝟎}  {𝐒 x} cx = 𝕟.[≡]-symmetry-raw {a = Bounded.𝐏(𝐒(x))}{b = x} (bounded-𝐏-𝐒-inverses{x = x} (𝕟.[≤]-maximum {a = x} ℕ.[≤]-of-[𝐒]))
  shift𝐏-some-value-gt {X = 𝐒(X)}{𝐒 c}{𝐒 x} cx
    rewrite extract-map ⦃ [≡]-equiv ⦄ {f = 𝕟.𝐒}{o = Optional.shift𝐏 c x} ⦃ shift𝐏-is-some (sub₂(𝕟._>_)(𝕟._≢_) {x} cx) ⦄
    rewrite 𝐏-step{Y = 𝐒(X)}{x = x} ⦃ 𝕟.[>]-to-positive {a = x} cx ⦄
    = shift𝐏-some-value-gt {X = X} {c} {x} cx

module _ where
  import      Numeral.Finite.Relation.Order.Proofs as 𝕟

  shift𝐒-value-lt : ∀{C X} {c : 𝕟(C)}{x : 𝕟(X)} → (cx : x 𝕟.< c) → (shift𝐒 c x 𝕟.≡ x)
  shift𝐒-value-lt {c = 𝐒 c}{x = 𝟎}   _   = <>
  shift𝐒-value-lt {c = 𝐒 c}{x = 𝐒 x} ord = shift𝐒-value-lt {c = c}{x = x} ord

  shift𝐒-value-gt : ∀{C X} {c : 𝕟(C)}{x : 𝕟(X)} → (cx : x 𝕟.≥ c) → (shift𝐒 c x 𝕟.≡ 𝐒(x))
  shift𝐒-value-gt {c = 𝟎}  {x = 𝟎}   _   = <>
  shift𝐒-value-gt {c = 𝟎}  {x = 𝐒 x} _   = 𝕟.[≡]-reflexivity-raw {a = x}
  shift𝐒-value-gt {c = 𝐒 c}{x = 𝐒 x} ord = shift𝐒-value-gt {c = c}{x = x} ord

shift𝐒-preserve-self-gt : ∀{N₁ N₂ X}{n₁ : 𝕟(N₁)}{n₂ : 𝕟(N₂)}{x : 𝕟(X)} → (n₁ 𝕟.≥ n₂) → (shift𝐒 (bound-𝐒(n₂)) (shift𝐒 n₁ x) ≡ shift𝐒 (𝐒(n₁)) (shift𝐒 n₂ x))
shift𝐒-preserve-self-gt {n₁ = 𝟎} {𝟎} {𝟎} ord = [≡]-intro
shift𝐒-preserve-self-gt {n₁ = 𝟎} {𝟎} {𝐒 x} ord = [≡]-intro
shift𝐒-preserve-self-gt {n₁ = 𝐒 n₁} {𝟎} {𝟎} ord = [≡]-intro
shift𝐒-preserve-self-gt {n₁ = 𝐒 n₁} {𝟎} {𝐒 x} ord = [≡]-intro
shift𝐒-preserve-self-gt {n₁ = 𝐒 n₁} {𝐒 n₂} {𝟎} ord = [≡]-intro
shift𝐒-preserve-self-gt {n₁ = 𝐒 n₁} {𝐒 n₂} {𝐒 x} ord
  rewrite shift𝐒-preserve-self-gt {n₁ = n₁} {n₂} {x} ord
  = [≡]-intro

{-
module _ where
  private variable N : ℕ
  private variable n₁ n₂ n₃ n₄ x : 𝕟(N)

  shift𝐒-preserve-self : ∀{x : 𝕟(N)} → (shift𝐒 n₁ (shift𝐒 n₂ x) ≡ shift𝐒 n₃ (shift𝐒 n₄ x))
  shift𝐒-preserve-self {n₁ = n₁} {n₂ = n₂} {n₃ = n₃} {n₄ = n₄} {x} = {!!}
-}

module _ where
  open import Data.Option
  open import Data.Option.Equiv.Id

  shift𝐏-shift𝐒-inverse₌ : ∀{C X}{c : 𝕟(C)}{x : 𝕟(X)} → (Optional.shift𝐏 c (shift𝐒 c x) ≡ Some(x))
  shift𝐏-shift𝐒-inverse₌ {c = 𝟎} {x = 𝟎} = [≡]-intro
  shift𝐏-shift𝐒-inverse₌ {c = 𝟎} {x = 𝐒 x} = [≡]-intro
  shift𝐏-shift𝐒-inverse₌ {c = 𝐒 c} {x = 𝟎} = [≡]-intro
  shift𝐏-shift𝐒-inverse₌ {c = 𝐒 c} {x = 𝐒 x}
    rewrite shift𝐏-shift𝐒-inverse₌ {c = c} {x = x}
    = [≡]-intro

  import      Numeral.Finite.Relation.Order.Proofs as 𝕟

  shift𝐏-shift𝐒-inverse : ∀{C₁ C₂ X}{c₁ : 𝕟(C₁)}{c₂ : 𝕟(C₂)}{x : 𝕟(X)} → (p1 : (x 𝕟.≥ c₁) ∨ (c₁ 𝕟.≤ c₂)) → (p2 : (x 𝕟.≥ c₂) ∨ (c₁ 𝕟.≥ c₂)) → (Optional.shift𝐏 c₁ (shift𝐒 c₂ x) ≡ Some x)
  shift𝐏-shift𝐒-inverse {c₁ = 𝟎} {c₂ = 𝟎} {x = 𝟎} p1 p2 = [≡]-intro
  shift𝐏-shift𝐒-inverse {c₁ = 𝟎} {c₂ = 𝟎} {x = 𝐒 x} p1 p2 = [≡]-intro
  shift𝐏-shift𝐒-inverse {c₁ = 𝟎} {c₂ = 𝐒 c₂} {x = 𝟎} p1 p2 = [∨]-elim [⊥]-elim [⊥]-elim p2
  shift𝐏-shift𝐒-inverse {c₁ = 𝟎} {c₂ = 𝐒 c₂} {x = 𝐒 x} p1 ([∨]-introₗ p2)
    rewrite [↔]-to-[←] ([≡][≡?]-equivalence {i = shift𝐒 c₂ x}{j = 𝐒 x}) (shift𝐒-value-gt{c = c₂}{x = x} p2)
    = [≡]-intro
  shift𝐏-shift𝐒-inverse {c₁ = 𝟎} {c₂ = 𝐒 c₂} {x = 𝐒 x} p1 ([∨]-introᵣ ())
  shift𝐏-shift𝐒-inverse {c₁ = 𝐒 c₁} {c₂ = 𝟎} {x = 𝟎} p1 p2 = [∨]-elim [⊥]-elim [⊥]-elim p1
  shift𝐏-shift𝐒-inverse {c₁ = 𝐒 c₁} {c₂ = c₂@𝟎} {x = 𝐒 x} p1 p2 = congruence₁(Option.map(𝐒)) (shift𝐏-shift𝐒-inverse {c₁ = c₁} {c₂ = c₂} {x = x} ([∨]-elim2 id [⊥]-elim p1) ([∨]-introₗ (𝕟.[≥]-minimum {a = x})))
  shift𝐏-shift𝐒-inverse {c₁ = 𝐒 c₁} {c₂ = 𝐒 c₂} {x = 𝟎} p1 p2 = [≡]-intro
  shift𝐏-shift𝐒-inverse {c₁ = 𝐒 c₁} {c₂ = 𝐒 c₂} {x = 𝐒 x} p1 p2 = congruence₁(Option.map(𝐒)) (shift𝐏-shift𝐒-inverse {c₁ = c₁} {c₂ = c₂} {x = x} p1 p2)

  {-
  module shift𝐏-shift𝐒-when-inverse where
    bound-proof : ∀{C₁ C₂ X}{c₁ : 𝕟(C₁)}{c₂ : 𝕟(C₂)}{x : 𝕟(X)} → (x 𝕟.≥ c₁) → (c₁ 𝕟.≥ c₂) → (shift𝐒 c₂ x 𝕟.≢ min c₁ (maximum{bound(𝐒(x))}))
    bound-proof {c₁ = 𝟎}       {c₂ = 𝟎}   {x = 𝟎}   p1 p2 = <>
    bound-proof {c₁ = 𝟎}       {c₂ = 𝟎}   {x = 𝐒 x} p1 p2 = <>
    bound-proof {c₁ = 𝐒 c₁}    {c₂ = 𝐒 c₂}{x = 𝐒 x} p1 p2 = bound-proof {c₁ = c₁}  {c₂ = c₂}{x = x} p1 p2
    bound-proof {c₁ = 𝐒 𝟎}     {c₂ = c₂@𝟎}{x = 𝐒 x} p1 p2 = bound-proof {c₁ = 𝟎}   {c₂ = c₂}{x = x} p1 p2
    bound-proof {c₁ = 𝐒 (𝐒 c₁)}{c₂ = c₂@𝟎}{x = 𝐒 x} p1 p2 = bound-proof {c₁ = 𝐒 c₁}{c₂ = c₂}{x = x} p1 <>

  shift𝐏-shift𝐒-when-inverse : ∀{C₁ C₂ X}{c₁ : 𝕟(C₁)}{c₂ : 𝕟(C₂)}{x : 𝕟(X)} → (p1 : x 𝕟.≥ c₁) → (p2 : c₁ 𝕟.≥ c₂) → (Option.extract(Optional.shift𝐏 c₁ (shift𝐒 c₂ x)) ⦃ shift𝐏-is-some (shift𝐏-shift𝐒-when-inverse.bound-proof{c₁ = c₁}{c₂ = c₂}{x = x} p1 p2) ⦄ ≡ x)
  shift𝐏-shift𝐒-when-inverse {c₁ = 𝟎} {c₂ = 𝟎} {x = 𝟎} p1 p2 = [≡]-intro
  shift𝐏-shift𝐒-when-inverse {c₁ = 𝟎} {c₂ = 𝟎} {x = 𝐒 x} p1 p2 = [≡]-intro
  shift𝐏-shift𝐒-when-inverse {c₁ = 𝟎} {c₂ = 𝐒 c₂} {x = 𝟎} _ ()
  shift𝐏-shift𝐒-when-inverse {c₁ = 𝟎} {c₂ = 𝐒 c₂} {x = 𝐒 x} _ ()
  shift𝐏-shift𝐒-when-inverse {c₁ = 𝐒 c₁} {c₂ = 𝟎} {x = 𝟎} ()
  shift𝐏-shift𝐒-when-inverse {c₁ = 𝐒 c₁} {c₂ = c₂@𝟎} {x = 𝐒 x} p1 p2 = extract-map{f = 𝐒}{o = Optional.shift𝐏 c₁ (𝐒 x)} ⦃ shift𝐏-is-some (shift𝐏-shift𝐒-when-inverse.bound-proof{c₁ = c₁}{c₂ = c₂}{x = x} p1 (𝕟.[≥]-minimum {a = c₁})) ⦄ 🝖 congruence₁(𝐒) (shift𝐏-shift𝐒-when-inverse {c₁ = c₁} {c₂ = c₂} {x = x} p1 (𝕟.[≥]-minimum {a = c₁}))
  shift𝐏-shift𝐒-when-inverse {c₁ = 𝐒 c₁} {c₂ = 𝐒 c₂} {x = 𝟎} p1 p2 = [≡]-intro
  shift𝐏-shift𝐒-when-inverse {c₁ = 𝐒 c₁} {c₂ = 𝐒 c₂} {x = 𝐒 x} p1 p2 = extract-map{f = 𝐒}{o = Optional.shift𝐏 c₁ (shift𝐒 c₂ x)} ⦃ shift𝐏-is-some (shift𝐏-shift𝐒-when-inverse.bound-proof{c₁ = c₁}{c₂ = c₂}{x = x} p1 p2) ⦄ 🝖 congruence₁(𝐒) (shift𝐏-shift𝐒-when-inverse {c₁ = c₁} {c₂ = c₂} {x = x} p1 p2)
  -}

{-
import      Data.Option.Functions as Option
open import Data.Option.Relation
import      Numeral.Natural.Relation as ℕ
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function

open import Functional
open import Type
private variable ℓ : Lvl.Level
private variable A B : Type{ℓ}

shift-None1 : ∀{n m}{c : 𝕟(m)}{x : 𝕟(ℕ.𝐒(n))} → (c 𝕟.≡ x) ∨ (c 𝕟.≥ 𝕟.maximum{ℕ.𝐒(n)}) → IsNone(Optional.shift c x)
shift-None1 {ℕ.𝟎}   {c = _}      {x = _}      _               = <>
shift-None1 {ℕ.𝐒 _} {c = 𝕟.𝟎}    {x = 𝕟.𝟎}    _               = <>
shift-None1 {ℕ.𝐒 _} {c = 𝕟.𝐒(c)} {x = 𝕟.𝟎}    ([∨]-introₗ ())
shift-None1 {ℕ.𝐒 _} {c = 𝕟.𝟎}    {x = 𝕟.𝐒(x)} ([∨]-introₗ ())
shift-None1 {ℕ.𝐒 _} {c = 𝕟.𝐒(c)} {x = 𝕟.𝐒(x)} cx              = [↔]-to-[→] IsNone-map (shift-None1 {c = c} {x = x} cx)

shift-None1 {ℕ.𝐒 _} {c = 𝕟.𝐒(c)} {x = 𝕟.𝟎}    ([∨]-introᵣ cn) = {!Optional.shift{3}{6} 5 3!}
shift-None1 {ℕ.𝐒 _} {c = 𝕟.𝟎}    {x = 𝕟.𝐒(x)} ([∨]-introᵣ cn) = {!!}
-- congruence₁(Option.map 𝕟.𝐒) (shift-None1 {c = c} {x = x} cx)

shift-Some1 : ∀{n m}{c : 𝕟(m)}{x : 𝕟(ℕ.𝐒(n))} → (c 𝕟.≢ x) → (c 𝕟.< 𝕟.maximum{ℕ.𝐒(n)}) → IsSome(Optional.shift c x)
shift-Some1 {ℕ.𝟎}   {c = _}      {x = _}      cx cn = {!!}
shift-Some1 {ℕ.𝐒 _} {c = 𝕟.𝟎}    {x = 𝕟.𝟎}    ()
shift-Some1 {ℕ.𝐒 _} {c = 𝕟.𝐒(c)} {x = 𝕟.𝟎}    cx cn = <>
shift-Some1 {ℕ.𝐒 _} {c = 𝕟.𝟎}    {x = 𝕟.𝐒(x)} cx cn = <>
shift-Some1 {ℕ.𝐒 _} {c = 𝕟.𝐒(c)} {x = 𝕟.𝐒(x)} cx cn = {!!}

test : ∀{n} ⦃ pos : ℕ.Positive(n) ⦄ {c : 𝕟(n)} → (shift𝐏ByRepeatRestrict' c 𝕟.𝟎 ≡ 𝕟.minimum{n})
test {ℕ.𝐒 _} {c = 𝕟.𝟎} = [≡]-intro
test {ℕ.𝐒 _} {c = 𝕟.𝐒 c} = [≡]-intro

test2 = {!shift𝐏BySkip{5} 5 5!}
-}
