{-# OPTIONS --with-K #-}

module Data.List.Proofs{ℓ₁} where

import Lvl
open import Functional
open import Data.Boolean
open import Data.List
import      Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs{ℓ₁}
open import Relator.EqualsOld{ℓ₁}
open import Relator.Equals.Proofs{ℓ₁}
open import Structure.Operator.Properties{ℓ₁}
open import Structure.Relator.Properties{ℓ₁}
import      Type

module _ {ℓ₁ ℓ₂ ℓ₃ : Lvl.Level} where
  open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₃}

  List-induction : ∀{T : Type{ℓ₂}}{P : List(T) → Stmt} → P(∅) → (∀(x : T)(l : List(T)) → P(l) → P(x ⊰ l)) → (∀{l : List(T)} → P(l))
  List-induction base next {∅} = base
  List-induction base next {x ⊰ l} = next(x)(l)(List-induction base next {l})

module _ {ℓ₂} where
  open Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
  open Type{ℓ₂}

  [++]-identityₗ : ∀{T : Type} → Identityₗ {ℓ₂}{List(T)} (_++_) ∅
  [++]-identityₗ = [≡]-intro

  [++]-identityᵣ : ∀{T : Type} → Identityᵣ {ℓ₂}{List(T)} (_++_) ∅
  [++]-identityᵣ {T} = List-induction{ℓ₁}{ℓ₂}{ℓ₂} base next where
    base : (∅ ++ ∅) ≡ ∅
    base = [≡]-intro

    next : ∀(x : T)(l : List(T)) → ((l ++ ∅) ≡ l) → (((x ⊰ l) ++ ∅) ≡ (x ⊰ l))
    next x _ stmt = [≡]-with(list ↦ x ⊰ list) stmt
    -- (l ++ ∅) ≡ l
    -- x ⊰ (l ++ ∅) ≡ x ⊰ l
    -- (x ⊰ l) ++ ∅ ≡ x ⊰ l
  {-# REWRITE [++]-identityᵣ #-}

  [++]-associativity : ∀{T} → Associativity {ℓ₂} {List(T)} (_++_)
  [++]-associativity {T} {l₀} {l₁} {l₂} = List-induction{ℓ₁}{ℓ₂}{ℓ₂} base next {l₀} where
    base : ((∅ ++ l₁) ++ l₂) ≡ (∅ ++ (l₁ ++ l₂))
    base = [≡]-intro
    -- l₁++l₂ = l₁++l₂
    -- ∅++(l₁++l₂) = (∅++l₁)++l₂

    next : ∀(x : T)(l : List(T)) → (((l ++ l₁) ++ l₂) ≡ (l ++ (l₁ ++ l₂))) → ((((x ⊰ l) ++ l₁) ++ l₂) ≡ ((x ⊰ l) ++ (l₁ ++ l₂)))
    next x _ stmt = [≡]-with(list ↦ x ⊰ list) stmt
    -- (l++l₁)++l₂ = l++(l₁++l₂)
    -- x ⊰ ((l++l₁)++l₂) = x ⊰ (l++(l₁++l₂))
    -- x ⊰ ((l++l₁)++l₂) = (x ⊰ l)++(l₁++l₂)
    -- (x ⊰ (l++l₁))++l₂ = (x ⊰ l)++(l₁++l₂)
    -- ((x ⊰ l)++l₁)++l₂ = (x ⊰ l)++(l₁++l₂)
  {-# REWRITE [++]-associativity #-}

  reverse-[++] : ∀{T}{l₁ l₂ : List(T)} → (reverse(l₁ ++ l₂) ≡ reverse(l₂) ++ reverse(l₁))
  reverse-[++] {T} {l₁} {l₂} = List-induction{ℓ₁}{ℓ₂}{ℓ₂} base next {l₁} where
    base : reverse(∅ ++ l₂) ≡ reverse(l₂) ++ reverse(∅)
    base =
      ([≡]-with(reverse) {l₂} ([≡]-intro))
      🝖 (symmetry [++]-identityᵣ)
    -- ∅++l = l //[++]-identityₗ
    -- reverse(∅++l) = l //[≡]-with(reverse) (..)
    --   l = l++∅

    -- ([≡]-with(reverse) {l₂} ([≡]-symmetry [++]-identityᵣ))
    -- l++∅ = l //[++]-identityᵣ
    -- l = l++∅ //[≡]-symmetry(..)
    -- reverse(l) = reverse(l++∅) //[≡]-with(reverse) (..)
    -- ∅++reverse(l) = reverse(l++∅)
    -- reverse(∅)++reverse(l) = reverse(l++∅)

    next : ∀(x : T)(l : List(T)) → (reverse(l ++ l₂) ≡ reverse(l₂) ++ reverse(l)) → (reverse((x ⊰ l) ++ l₂) ≡ reverse(l₂) ++ reverse(x ⊰ l))
    next x l stmt =
      ([≡]-with(list ↦ list ++ (singleton x)) stmt)
      🝖 ([++]-associativity {_} {reverse(l₂)} {reverse(l)} {singleton x})
    -- reverse(l₁++l₂) = reverse(l₂)++reverse(l₁)
    -- reverse(l₁++l₂)++(singleton x) = (reverse(l₂)++reverse(l₁))++(singleton x)
    -- reverse(l₁++l₂)++(singleton x) = reverse(l₂)++(reverse(l₁)++(singleton x))
    -- reverse(l₁++l₂)++(singleton x) = reverse(l₂)++reverse(x ⊰ l₁)
    -- reverse(x ⊰ (l₁++l₂)) = reverse(l₂)++reverse(x ⊰ l₁)
    -- reverse((x ⊰ l₁)++l₂) = reverse(l₂)++reverse(x ⊰ l₁)

    -- reverse (x ⊰ l) = (reverse l) ++ (singleton x)
    -- _++_ ∅ b = b
    -- _++_ (elem ⊰ rest) b = elem ⊰ (rest ++ b)
  {-# REWRITE reverse-[++] #-}

  length-[∅] : ∀{T : Type} → (length(∅{_}{T}) ≡ 0)
  length-[∅] = [≡]-intro

  length-singleton : ∀{T : Type}{a : T} → (length(singleton(a)) ≡ 1)
  length-singleton = [≡]-intro

  length-[++] : ∀{T : Type}{l₁ l₂ : List(T)} → (length(l₁ ++ l₂) ≡ length(l₁) + length(l₂))
  length-[++] {T} {l₁} {l₂} = List-induction{ℓ₁}{ℓ₂}{Lvl.𝟎} base next {l₁} where
    base : length(∅ ++ l₂) ≡ length{ℓ₂}{T}(∅) + length(l₂)
    base = symmetry [+]-identityₗ

    next : ∀(x : T)(l : List(T)) → (length(l ++ l₂) ≡ length(l) + length(l₂)) → (length((x ⊰ l) ++ l₂) ≡ length(x ⊰ l) + length(l₂))
    next x l stmt =
      ([≡]-with(𝐒) stmt)
      🝖 (symmetry([+1]-commutativity {length(l)} {length(l₂)}))
    -- length(l++l₂) = length(l)+length(l₂)
    -- length(l++l₂) = length(l₂)+length(l)
    -- 𝐒(length(l++l₂)) = 𝐒(length(l₂)+length(l))
    -- 𝐒(length(l++l₂)) = length(l₂)+𝐒(length(l))
    -- 𝐒(length(l++l₂)) = 𝐒(length(l))+length(l₂)
    -- length(x ⊰ (l++l₂)) = length(x ⊰ l)+length(l₂) //TODO: Is this step really okay? 𝐒 cannot uniquely identify that x was the precedant

  length-reverse : ∀{T : Type}{l : List(T)} → length(reverse(l)) ≡ length(l)
  length-reverse {T} = List-induction{ℓ₁}{ℓ₂}{Lvl.𝟎} base next where
    base : length{_}{T}(reverse(∅)) ≡ length{_}{T}(∅)
    base = [≡]-intro

    next : ∀(x : T)(l : List(T)) → (length(reverse(l)) ≡ length(l)) → (length(reverse(x ⊰ l)) ≡ length(x ⊰ l))
    next x l stmt =
      ((length-[++] {T} {reverse(l)} {singleton(x)}))
      🝖 ([≡]-with(𝐒) stmt)
      -- length(reverse(x ⊰ l))
      -- = length((reverse l) ++ (singleton x))
      -- = length(reverse l) + length(singleton x)
      -- = length(reverse l) + 1
      -- = 𝐒(length(reverse l))

      -- length(x ⊰ l)
      -- = 𝐒(length(l))

  length-repeat : ∀{T : Type}{x : T}{n} → (length(repeat(x)(n)) ≡ n)
  length-repeat{_}{_}{𝟎}    = [≡]-intro
  length-repeat{T}{x}{𝐒(n)} = [≡]-with(𝐒) (length-repeat{T}{x}{n})
  {-# REWRITE length-repeat #-}

  length-tail : ∀{T : Type}{l : List(T)} → (length(tail(l)) ≡ 𝐏(length(l)))
  length-tail{T}{∅}     = [≡]-intro
  length-tail{T}{_ ⊰ l} = [≡]-intro
    -- length(tail(x ⊰ l))
    -- = length(l)

    -- 𝐏(length(x ⊰ l))
    -- = 𝐏(𝐒(length(l)))
    -- = length(l))

  [⊰]-cancellationₗ : ∀{T} → Cancellationₗ {ℓ₂}{T} (_⊰_)
  [⊰]-cancellationₗ {_} {x} {∅}      {∅}     _          = [≡]-intro
  [⊰]-cancellationₗ {_} {x} {∅}      {_ ⊰ _} ()
  [⊰]-cancellationₗ {_} {x} {_ ⊰ _}  {∅}     ()
  [⊰]-cancellationₗ {_} {x} {_ ⊰ l₁} {_ ⊰ l₂} [≡]-intro = [≡]-intro

  [⊰]-cancellationᵣ : ∀{T} → Cancellationᵣ {ℓ₂}{T} (_⊰_)
  [⊰]-cancellationᵣ {_} {∅}     [≡]-intro = [≡]-intro
  [⊰]-cancellationᵣ {_} {_ ⊰ _} [≡]-intro = [≡]-intro

  [++]-cancellationₗ : ∀{T} → Cancellationₗ {ℓ₂}{List(T)} (_++_)
  [++]-cancellationₗ {_} {∅}     [≡]-intro = [≡]-intro
  [++]-cancellationₗ {_} {x ⊰ l} proof     = [++]-cancellationₗ {_} {l} ([⊰]-cancellationₗ proof)
    -- (x ⊰ l) ++ a
    -- = x ⊰ (l ++ a)

    -- ((x ⊰ l) ++ a) ≡ ((x ⊰ l) ++ b)
    -- x ⊰ (l ++ a) ≡ x ⊰ (l ++ b)
    -- l ++ a ≡ l ++ b
    -- a ≡ b

  -- TODO: [++]-cancellationᵣ : ∀{T} → Cancellationₗ {ℓ₂}{List(T)} (_++_)
    -- (a ++ (x ⊰ l)) ≡ (b ++ (x ⊰ l))
    -- (a ++ (singleton(x) ++ l)) ≡ (b ++ (singleton(x) ++ l))
    -- ((a ++ singleton(x)) ++ l) ≡ (b ++ (singleton(x) ++ l))
    -- ((a ++ singleton(x)) ++ l) ≡ ((b ++ singleton(x)) ++ l)
    -- and here, pattern match a and b?

    -- ((x₁ ⊰ a) ++ l) ≡ ((x₂ ⊰ b) ++ l)
    -- x₁ ⊰ (a ++ l) ≡ x₂ ⊰ (b ++ l)
    -- This is getting nowhere...

  length-multiply : ∀{T : Type}{l : List(T)}{n : ℕ} → (length(multiply(l)(n)) ≡ length(l) ⋅ n)
  length-multiply{T}{l}{𝟎}    = [≡]-intro
  length-multiply{T}{l}{𝐒(n)} =
    length-[++] {T} {l}{multiply l n}
    🝖 [≡]-with(expr ↦ length(l) + expr) (length-multiply{T}{l}{n})

module _ {ℓ₂} where
  open Logic.Propositional
  open Type{ℓ₂}

  length-isEmpty : ∀{T : Type}{L : List(T)} → (length(L) ≡ 0) ↔ (isEmpty(L) ≡ 𝑇)
  length-isEmpty{_}{∅} = [↔]-intro (const [≡]-intro) (const [≡]-intro)
  length-isEmpty{_}{x ⊰ L} = [↔]-intro l r where
    l : (length(x ⊰ L) ≡ 0) ← (isEmpty(x ⊰ L) ≡ 𝑇)
    l()

    r : (length(x ⊰ L) ≡ 0) → (isEmpty(x ⊰ L) ≡ 𝑇)
    r()

-- TODO: Empty list is prefix and suffix of everything
-- TODO: Whole list is prefix and suffix of everything
-- TODO: multiply(singleton(l))(n) = repeat(l)(n)
-- TODO: reverse(reverse(l)) = l
