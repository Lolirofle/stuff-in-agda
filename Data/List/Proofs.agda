module Data.List.Proofs where

import Lvl
open import Functional
open import Data.Boolean
open import Data.Option
open import Data.Either.Proofs
open import Data.List
open import Logic
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Type

module _ {ℓ₁ ℓ₂ : Lvl.Level} where
  List-induction : ∀{T : Type{ℓ₁}}{P : List(T) → Stmt{ℓ₂}} → P(∅) → (∀(x : T)(l : List(T)) → P(l) → P(x ⊰ l)) → (∀{l : List(T)} → P(l))
  List-induction base next {∅} = base
  List-induction base next {x ⊰ l} = next(x)(l)(List-induction base next {l})

module _ {ℓ} where
  instance
    [++]-identityₗ : ∀{T : Type{ℓ}} → Identityₗ{T₁ = List(T)} (_++_) ∅
    Identityₗ.proof([++]-identityₗ) = [≡]-intro

  [++]-identityᵣ-raw : ∀{T : Type{ℓ}} → Names.Identityᵣ (_++_) ∅
  [++]-identityᵣ-raw {T} = List-induction base next where
    base : (∅ ++ ∅) ≡ ∅
    base = [≡]-intro

    next : ∀(x : T)(l : List(T)) → ((l ++ ∅) ≡ l) → (((x ⊰ l) ++ ∅) ≡ (x ⊰ l))
    next x _ stmt = [≡]-with(list ↦ x ⊰ list) stmt
    -- (l ++ ∅) ≡ l
    -- x ⊰ (l ++ ∅) ≡ x ⊰ l
    -- (x ⊰ l) ++ ∅ ≡ x ⊰ l
  {-# REWRITE [++]-identityᵣ-raw #-}

  instance
    [++]-identityᵣ : ∀{T : Type{ℓ}} → Identityᵣ{T₁ = List(T)} (_++_) ∅
    Identityᵣ.proof([++]-identityᵣ) = [++]-identityᵣ-raw

  [++]-associativity-raw : ∀{T : Type{ℓ}} → Names.Associativity(_++_)
  [++]-associativity-raw {T} {l₀} {l₁} {l₂} = List-induction base next {l₀} where
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
  {-# REWRITE [++]-associativity-raw #-}

  instance
    [++]-associativity : ∀{T : Type{ℓ}} → Associativity{T = List(T)} (_++_)
    Associativity.proof([++]-associativity) = [≡]-intro

  reverse-[++] : ∀{T : Type{ℓ}}{l₁ l₂ : List(T)} → (reverse(l₁ ++ l₂) ≡ reverse(l₂) ++ reverse(l₁))
  reverse-[++] {T} {l₁} {l₂} = List-induction base next {l₁} where
    base : reverse(∅ ++ l₂) ≡ reverse(l₂) ++ reverse(∅)
    base =
      ([≡]-with(reverse) {l₂} ([≡]-intro))
      🝖 (symmetry(_≡_) [++]-identityᵣ-raw)
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
      🝖 ([++]-associativity-raw {_} {reverse(l₂)} {reverse(l)} {singleton x})
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

  length-[∅] : ∀{T : Type{ℓ}} → (length(∅ {T = T}) ≡ 0)
  length-[∅] = [≡]-intro

  length-singleton : ∀{T : Type{ℓ}}{a : T} → (length(singleton(a)) ≡ 1)
  length-singleton = [≡]-intro

  length-[++] : ∀{T : Type{ℓ}}{l₁ l₂ : List(T)} → (length(l₁ ++ l₂) ≡ length(l₁) + length(l₂))
  length-[++] {T} {l₁} {l₂} = List-induction base next {l₁} where
    base : length(∅ ++ l₂) ≡ length{ℓ}{T}(∅) + length(l₂)
    base = symmetry(_≡_) (identityₗ(_+_)(0))

    next : ∀(x : T)(l : List(T)) → (length(l ++ l₂) ≡ length(l) + length(l₂)) → (length((x ⊰ l) ++ l₂) ≡ length(x ⊰ l) + length(l₂))
    next x l stmt =
      ([≡]-with(𝐒) stmt)
      🝖 (symmetry(_≡_) ([+1]-commutativity {length(l)} {length(l₂)}))
    -- length(l++l₂) = length(l)+length(l₂)
    -- length(l++l₂) = length(l₂)+length(l)
    -- 𝐒(length(l++l₂)) = 𝐒(length(l₂)+length(l))
    -- 𝐒(length(l++l₂)) = length(l₂)+𝐒(length(l))
    -- 𝐒(length(l++l₂)) = 𝐒(length(l))+length(l₂)
    -- length(x ⊰ (l++l₂)) = length(x ⊰ l)+length(l₂) //TODO: Is this step really okay? 𝐒 cannot uniquely identify that x was the precedant

  length-reverse : ∀{T : Type{ℓ}}{l : List(T)} → length(reverse(l)) ≡ length(l)
  length-reverse {T} = List-induction base next where
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

  length-repeat : ∀{T : Type{ℓ}}{x : T}{n} → (length(repeat(x)(n)) ≡ n)
  length-repeat{_}{_}{𝟎}    = [≡]-intro
  length-repeat{T}{x}{𝐒(n)} = [≡]-with(𝐒) (length-repeat{T}{x}{n})
  {-# REWRITE length-repeat #-}

  length-tail : ∀{T : Type{ℓ}}{l : List(T)} → (length(tail(l)) ≡ 𝐏(length(l)))
  length-tail{T}{∅}     = [≡]-intro
  length-tail{T}{_ ⊰ l} = [≡]-intro
    -- length(tail(x ⊰ l))
    -- = length(l)

    -- 𝐏(length(x ⊰ l))
    -- = 𝐏(𝐒(length(l)))
    -- = length(l))

  instance
    [⊰]-cancellationₗ : ∀{T : Type{ℓ}} → Cancellationₗ {T₁ = T} (_⊰_)
    Cancellationₗ.proof([⊰]-cancellationₗ) = proof where
      proof : Names.Cancellationₗ(_⊰_)
      proof {x} {∅}      {∅}     _          = [≡]-intro
      proof {x} {∅}      {_ ⊰ _} ()
      proof {x} {_ ⊰ _}  {∅}     ()
      proof {x} {x1 ⊰ l1} {x2 ⊰ l2} p = [≡]-with(tail) p

  instance
    [⊰]-cancellationᵣ : ∀{T : Type{ℓ}} → Cancellationᵣ {T₁ = T} (_⊰_)
    Cancellationᵣ.proof([⊰]-cancellationᵣ) = proof where
      proof : Names.Cancellationᵣ(_⊰_)
      proof {∅}     [≡]-intro = [≡]-intro
      proof {x ⊰ l} p = Right-injectivity([≡]-with(firstElem) p)

  [⊰]-general-cancellationᵣ : ∀{T : Type{ℓ}}{x₁ x₂ : T}{l₁ l₂} → ((x₁ ⊰ l₁) ≡ (x₂ ⊰ l₂)) → (l₁ ≡ l₂)
  [⊰]-general-cancellationᵣ p = [≡]-with(tail) p

  [⊰]-general-cancellationₗ : ∀{T : Type{ℓ}}{x₁ x₂ : T}{l₁ l₂} → ((x₁ ⊰ l₁) ≡ (x₂ ⊰ l₂)) → (x₁ ≡ x₂)
  [⊰]-general-cancellationₗ {_} {x1} {x2} {∅}      {∅}      [≡]-intro = [≡]-intro
  [⊰]-general-cancellationₗ {_} {x1} {x2} {∅}      {x ⊰ l2} p with [⊰]-general-cancellationᵣ p
  ...                                                                | ()
  [⊰]-general-cancellationₗ {_} {x1} {x2} {xl1 ⊰ l1} {xl2 ⊰ l2} p = Right-injectivity([≡]-with(firstElem) p)

  [∅][⊰]-unequal : ∀{T : Type{ℓ}}{x : T}{l} → ¬(∅ ≡ x ⊰ l)
  [∅][⊰]-unequal {_} {x} {l} ()

  [⊰]-unequal : ∀{T : Type{ℓ}}{x : T}{l} → ¬(x ⊰ l ≡ l)
  [⊰]-unequal {_} {x} {l} ()

  {- TODO
  postulate [⊰][++]-unequal : ∀{T : Type{ℓ}}{x : T}{a l} → ¬(a ++ (x ⊰ l) ≡ l)
  -- [⊰][++]-unequal {T} {x} {x₁ ⊰ a} {x₂ ⊰ l} p = {!!}

  [++]-cancellation-of-[∅]l : ∀{T : Type{ℓ}}{a b : List(T)} → (a ++ b ≡ b) → (a ≡ ∅)
  [++]-cancellation-of-[∅]l {_} {∅}    {b}      _ = [≡]-intro
  [++]-cancellation-of-[∅]l {_} {x ⊰ a} {y ⊰ b} p = [⊥]-elim([⊰][++]-unequal([⊰]-general-cancellationᵣ p))

  instance
    [++]-cancellationₗ : ∀{T : Type{ℓ}} → Cancellationₗ {T₁ = List(T)} (_++_)
    Cancellationₗ.proof([++]-cancellationₗ) = proof where
      proof : Names.Cancellationₗ (_++_)
      proof {∅}     p = p
      proof {x ⊰ l} p  = proof {l} (cancellationₗ(_⊰_) p)
      -- (x ⊰ l) ++ a
      -- = x ⊰ (l ++ a)

      -- ((x ⊰ l) ++ a) ≡ ((x ⊰ l) ++ b)
      -- x ⊰ (l ++ a) ≡ x ⊰ (l ++ b)
      -- l ++ a ≡ l ++ b
      -- a ≡ b

  instance
    [++]-cancellationᵣ : ∀{T : Type{ℓ}} → Cancellationᵣ {T₁ = List(T)} (_++_)
    Cancellationᵣ.proof([++]-cancellationᵣ) {a}{b} = proof {a}{b} where
      proof : Names.Cancellationᵣ(_++_)
      proof {l}      {∅}     {∅}      p = [≡]-intro
      proof {x₁ ⊰ l} {∅}     {x ⊰ b}  p = [⊥]-elim([⊰][++]-unequal(symmetry(_≡_) ([⊰]-general-cancellationᵣ p)))
      proof {x₁ ⊰ l} {x ⊰ a}  {∅}     p = [⊥]-elim([⊰][++]-unequal([⊰]-general-cancellationᵣ p))
      proof {l}      {x ⊰ a} {x₁ ⊰ b} p = [≡]-with-op(_⊰_) ([⊰]-general-cancellationₗ p) (proof{l}{a}{b} ([⊰]-general-cancellationᵣ p))
  -}

  length-[++^] : ∀{T : Type{ℓ}}{l : List(T)}{n : ℕ} → (length(l ++^ n) ≡ length(l) ⋅ n)
  length-[++^]{T}{l}{𝟎}    = [≡]-intro
  length-[++^]{T}{l}{𝐒(n)} =
    length-[++] {T} {l}{l ++^ n}
    🝖 [≡]-with(expr ↦ length(l) + expr) (length-[++^]{T}{l}{n})

module _ {ℓ} where
  length-isEmpty : ∀{T : Type{ℓ}}{L : List(T)} → (length(L) ≡ 0) ↔ (isEmpty(L) ≡ 𝑇)
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

module _ {ℓ} {T : Type{ℓ}} where
  first-0-length : ∀{L : List(T)} → (first(0)(L) ≡ ∅)
  first-0-length {∅}    = [≡]-intro
  first-0-length {x ⊰ L} = [≡]-intro

  first-of-∅ : ∀{n} → (first(n)(∅ {T = T}) ≡ ∅)
  first-of-∅ {𝟎}   = [≡]-intro
  first-of-∅ {𝐒 n} = [≡]-intro
