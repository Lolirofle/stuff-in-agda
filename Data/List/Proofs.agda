module Data.List.Proofs where

import Lvl
open import Functional
open import Data.Boolean
open import Data.Option hiding (map)
open import Data.Either
open import Data.Either.Proofs
open import Data.List
open import Logic
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function.Domain
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

module _ {ℓ₁ ℓ₂ : Lvl.Level} where
  List-induction : ∀{T : Type{ℓ₁}}{P : List(T) → Stmt{ℓ₂}} → P(∅) → (∀(x : T)(l : List(T)) → P(l) → P(x ⊰ l)) → (∀{l : List(T)} → P(l))
  List-induction base next {∅} = base
  List-induction base next {x ⊰ l} = next(x)(l)(List-induction base next {l})

module _ {ℓ} where
  instance
    [++]-identityₗ : ∀{T : Type{ℓ}} → Identityₗ{T₁ = List(T)} (_++_) ∅
    Identityₗ.proof([++]-identityₗ) = [≡]-intro

  [++]-identityᵣ-raw : ∀{T : Type{ℓ}} → Names.Identityᵣ (Functional.swap(foldᵣ{T = T}(_⊰_))) ∅
  [++]-identityᵣ-raw {x = ∅}     = [≡]-intro
  [++]-identityᵣ-raw {x = x ⊰ l} = [≡]-with(x ⊰_) ([++]-identityᵣ-raw {x = l})
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

  instance
    [++]-associativity : ∀{T : Type{ℓ}} → Associativity{T = List(T)} (_++_)
    Associativity.proof([++]-associativity {T}) {x}{y}{z} = [++]-associativity-raw {T} {x}{y}{z}

  postpend-of-prepend : ∀{T : Type{ℓ}}{a b}{l : List(T)} → (postpend a (b ⊰ l) ≡ b ⊰ postpend a l)
  postpend-of-prepend = [≡]-intro

  reverse-postpend : ∀{T : Type{ℓ}}{a}{l : List(T)} → (reverse(postpend a l) ≡ a ⊰ reverse l)
  reverse-postpend {l = ∅}     = [≡]-intro
  reverse-postpend {l = x ⊰ l} = [≡]-with(postpend x) (reverse-postpend {l = l})

  prepend-[++] : ∀{T : Type{ℓ}}{a}{l : List(T)} → (a ⊰ l ≡ singleton(a) ++ l)
  prepend-[++] = [≡]-intro

  postpend-[++] : ∀{T : Type{ℓ}}{a}{l : List(T)} → (postpend a l ≡ l ++ singleton(a))
  postpend-[++] {l = ∅}     = [≡]-intro
  postpend-[++] {l = x ⊰ l} = [≡]-with(x ⊰_) (postpend-[++] {l = l})

  postpend-of-[++] : ∀{T : Type{ℓ}}{a}{l₁ l₂ : List(T)} → (postpend a (l₁ ++ l₂) ≡ l₁ ++ postpend a l₂)
  postpend-of-[++] {T} {a} {∅}      {l₂} = [≡]-intro
  postpend-of-[++] {T} {a} {x ⊰ l₁} {l₂} = [≡]-with(x ⊰_) (postpend-of-[++] {T} {a} {l₁} {l₂})

  map-postpend : ∀{ℓ₂}{A : Type{ℓ}}{B : Type{ℓ₂}}{f : A → B}{a}{l : List(A)} → (map f(postpend a l) ≡ postpend (f(a)) (map f(l)))
  map-postpend {f = f} {l = ∅}     = [≡]-intro
  map-postpend {f = f} {l = x ⊰ l} = [≡]-with (f(x) ⊰_) map-postpend

  reverse-[++] : ∀{T : Type{ℓ}}{l₁ l₂ : List(T)} → (reverse(l₁ ++ l₂) ≡ reverse(l₂) ++ reverse(l₁))
  reverse-[++] {T} {∅}      {l₂} = [≡]-intro
  reverse-[++] {T} {x ⊰ l₁} {l₂} = [≡]-with(postpend x) (reverse-[++] {T} {l₁} {l₂}) 🝖 postpend-of-[++] {l₁ = reverse l₂} {l₂ = reverse l₁}

  map-[++] : ∀{ℓ₂}{A : Type{ℓ}}{B : Type{ℓ₂}}{f : A → B}{l₁ l₂ : List(A)} → (map f(l₁ ++ l₂) ≡ map f(l₁) ++ map f(l₂))
  map-[++] {f = f} {l₁ = ∅} {∅} = [≡]-intro
  map-[++] {f = f} {l₁ = ∅} {x ⊰ l₂} = [≡]-intro
  map-[++] {f = f} {l₁ = x ⊰ l₁} {l₂} = [≡]-with(f(x) ⊰_) (map-[++] {f = f} {l₁ = l₁} {l₂})

  length-[∅] : ∀{T : Type{ℓ}} → (length(∅ {T = T}) ≡ 0)
  length-[∅] = [≡]-intro

  length-singleton : ∀{T : Type{ℓ}}{a : T} → (length(singleton(a)) ≡ 1)
  length-singleton = [≡]-intro

  length-postpend : ∀{T : Type{ℓ}}{a : T}{l : List(T)} → (length(postpend a l) ≡ 𝐒(length l))
  length-postpend {l = ∅}     = [≡]-intro
  length-postpend {l = x ⊰ l} = [≡]-with(𝐒) (length-postpend {l = l})
  -- {-# REWRITE length-postpend #-}

  length-[++] : ∀{T : Type{ℓ}}{l₁ l₂ : List(T)} → (length(l₁ ++ l₂) ≡ length(l₁) + length(l₂))
  length-[++] {T} {l₁} {l₂} = List-induction base next {l₁} where
    base : length(∅ ++ l₂) ≡ length{ℓ}{T}(∅) + length(l₂)
    base = symmetry(_≡_) (identityₗ(_+_)(0))

    next : ∀(x : T)(l : List(T)) → (length(l ++ l₂) ≡ length(l) + length(l₂)) → (length((x ⊰ l) ++ l₂) ≡ length(x ⊰ l) + length(l₂))
    next x l stmt = ([≡]-with(𝐒) stmt) 🝖 (symmetry(_≡_) ([+1]-commutativity {length(l)} {length(l₂)}))
    -- length(l++l₂) = length(l)+length(l₂) = length(l₂)+length(l)
    -- 𝐒(length(l++l₂)) = 𝐒(length(l₂)+length(l))  = length(l₂)+𝐒(length(l))  = 𝐒(length(l))+length(l₂)
    -- length(x ⊰ (l++l₂)) = length(x ⊰ l)+length(l₂)

  length-reverse : ∀{T : Type{ℓ}}{l : List(T)} → (length(reverse(l)) ≡ length(l))
  length-reverse {l = ∅}     = [≡]-intro
  length-reverse {l = x ⊰ l} = length-postpend{a = x}{l = reverse l} 🝖 [≡]-with(𝐒) (length-reverse {l = l})

  length-repeat : ∀{T : Type{ℓ}}{x : T}{n} → (length(repeat(x)(n)) ≡ n)
  length-repeat{n = 𝟎}    = [≡]-intro
  length-repeat{n = 𝐒(n)} = [≡]-with(𝐒) (length-repeat{n = n})

  length-tail : ∀{T : Type{ℓ}}{l : List(T)} → (length(tail(l)) ≡ 𝐏(length(l)))
  length-tail{T}{∅}     = [≡]-intro
  length-tail{T}{_ ⊰ l} = [≡]-intro

  length-map : ∀{ℓ₂}{A : Type{ℓ}}{B : Type{ℓ₂}}{f : A → B}{l : List(A)} → (length(map f(l)) ≡ length(l))
  length-map {l = ∅}     = [≡]-intro
  length-map {l = x ⊰ l} = [≡]-with(𝐒) (length-map {l = l})

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
      proof {x ⊰ l} p = injective(Right) ([≡]-with(firstElem) p)

  [⊰]-general-cancellationᵣ : ∀{T : Type{ℓ}}{x₁ x₂ : T}{l₁ l₂} → ((x₁ ⊰ l₁) ≡ (x₂ ⊰ l₂)) → (l₁ ≡ l₂)
  [⊰]-general-cancellationᵣ p = [≡]-with(tail) p

  [⊰]-general-cancellationₗ : ∀{T : Type{ℓ}}{x₁ x₂ : T}{l₁ l₂} → ((x₁ ⊰ l₁) ≡ (x₂ ⊰ l₂)) → (x₁ ≡ x₂)
  [⊰]-general-cancellationₗ {_} {x1} {x2} {∅}      {∅}      [≡]-intro = [≡]-intro
  [⊰]-general-cancellationₗ {_} {x1} {x2} {∅}      {x ⊰ l2} p with [⊰]-general-cancellationᵣ p
  ...                                                                | ()
  [⊰]-general-cancellationₗ {_} {x1} {x2} {xl1 ⊰ l1} {xl2 ⊰ l2} p = injective(Right) ([≡]-with(firstElem) p)

  [∅][⊰]-unequal : ∀{T : Type{ℓ}}{x : T}{l} → ¬(∅ ≡ x ⊰ l)
  [∅][⊰]-unequal {_} {x} {l} ()

  [⊰]-unequal : ∀{T : Type{ℓ}}{x : T}{l} → ¬(x ⊰ l ≡ l)
  [⊰]-unequal {_} {x} {l} ()

  [∅]-postpend-unequal : ∀{T : Type{ℓ}}{x : T}{l} → ¬(postpend x l ≡ ∅)
  [∅]-postpend-unequal {_} {_} {∅}     ()
  [∅]-postpend-unequal {_} {_} {_ ⊰ _} ()

  postpend-unequal : ∀{T : Type{ℓ}}{x : T}{l} → ¬(postpend x l ≡ l)
  postpend-unequal {_} {x} {∅} ()
  postpend-unequal {_} {x} {y ⊰ l} p = postpend-unequal {_} {x} {l} (cancellationₗ(_⊰_) p)

  {-
  [⊰][++]-unequal : ∀{T : Type{ℓ}}{x : T}{a l} → ¬(a ++ (x ⊰ l) ≡ l)
  [⊰][++]-unequal {x = x} {a} {l} p = {![≡]-with(_++ l) postpend-[++] 🝖 associativity(_++_) {x = a}{y = singleton x}{z = l} 🝖 p!} where
    proof : ∀{l} → ¬(postpend x a ++ l ≡ l)
    proof {∅}       = [∅]-postpend-unequal
    proof {x ⊰ l} p = proof {l} {!!}
  -- associativity(_++_) {x = a}{y = singleton x}{z = l} 🝖 p
  -- [⊰][++]-unequal {T} {x} {x₁ ⊰ a} {x₂ ⊰ l} p = [⊰][++]-unequal {T} {x} {a} {x₂ ⊰ l} ({!!} 🝖 p)

  [++]-cancellation-of-[∅]l : ∀{T : Type{ℓ}}{a b : List(T)} → (a ++ b ≡ b) → (a ≡ ∅)
  [++]-cancellation-of-[∅]l {_} {∅}    {b}      _ = [≡]-intro
  [++]-cancellation-of-[∅]l {_} {x ⊰ a} {y ⊰ b} p = [⊥]-elim([⊰][++]-unequal([⊰]-general-cancellationᵣ p))
  -}

  instance
    [++]-cancellationₗ : ∀{T : Type{ℓ}} → Cancellationₗ(_++_ {T = T})
    Cancellationₗ.proof([++]-cancellationₗ {T}) {x}{y}{z} = proof {x}{y}{z} where
      proof : Names.Cancellationₗ (_++_)
      proof {∅}     p = p
      proof {x ⊰ l} p  = proof {l} (cancellationₗ(_⊰_) p)

  {-
  instance
    [++]-cancellationᵣ : ∀{T : Type{ℓ}} → Cancellationᵣ {T₁ = List(T)} (_++_)
    Cancellationᵣ.proof([++]-cancellationᵣ) {a}{b} = proof {a}{b} where
      proof : Names.Cancellationᵣ(_++_)
      proof {l}      {∅}     {∅}      p = [≡]-intro
      proof {l}      {x ⊰ a} {x₁ ⊰ b} p = [≡]-with-op(_⊰_) ([⊰]-general-cancellationₗ p) (proof{l}{a}{b} ([⊰]-general-cancellationᵣ p))
      proof {∅}      {∅}     {x ⊰ b}  p = [++]-identityᵣ-raw 🝖 p
      proof {x₁ ⊰ l} {∅}     {x ⊰ b}  p = [⊥]-elim([⊰][++]-unequal(symmetry(_≡_) ([⊰]-general-cancellationᵣ p)))
      proof {∅}      {x ⊰ a}  {∅}     p = p
      proof {x₁ ⊰ l} {x ⊰ a}  {∅}     p = [⊥]-elim([⊰][++]-unequal([⊰]-general-cancellationᵣ p))
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

module _ {ℓ} {T : Type{ℓ}} where
  multiply-singleton-repeat : ∀{l : List(T)}{n} → (singleton(l) ++^ n ≡ repeat(l)(n))
  multiply-singleton-repeat {l} {𝟎}   = [≡]-intro
  multiply-singleton-repeat {l} {𝐒 n} = [≡]-with(l ⊰_) (multiply-singleton-repeat {l} {n})

module _ {ℓ} {T : Type{ℓ}} where
  reverse-involution : ∀{l : List(T)} → (reverse(reverse(l)) ≡ l)
  reverse-involution {∅} = [≡]-intro
  reverse-involution {x ⊰ l} = reverse-postpend {a = x}{l = reverse l} 🝖 [≡]-with(x ⊰_) (reverse-involution {l})

module _ {ℓ} {T : Type{ℓ}} where
  first-0-length : ∀{L : List(T)} → (first(0)(L) ≡ ∅)
  first-0-length {∅}    = [≡]-intro
  first-0-length {x ⊰ L} = [≡]-intro
  {-# REWRITE first-0-length #-}

  first-of-∅ : ∀{n} → (first(n)(∅ {T = T}) ≡ ∅)
  first-of-∅ {𝟎}   = [≡]-intro
  first-of-∅ {𝐒 n} = [≡]-intro

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type{ℓ₁}} {B : Type{ℓ₂}} {C : Type{ℓ₃}} {f : B → C}{g : A → B} where
  map-preserves-[∘] : ∀{l} → (map(f ∘ g)(l) ≡ ((map f) ∘ (map g))(l))
  map-preserves-[∘] {∅}     = [≡]-intro
  map-preserves-[∘] {x ⊰ l} = [≡]-with(f(g(x)) ⊰_) (map-preserves-[∘] {l})

  -- map-preserves-[∘]-sym = \{l} → symmetry(_≡_) (map-preserves-[∘] {l})
  -- {-# REWRITE map-preserves-[∘]-sym #-}

module _ {ℓ} {T : Type{ℓ}} where
  map-preserves-id : ∀{l : List(T)} → (map id(l) ≡ l)
  map-preserves-id {∅} = [≡]-intro
  map-preserves-id {x ⊰ l} = [≡]-with(x ⊰_) (map-preserves-id {l})
  {-# REWRITE map-preserves-id #-}
