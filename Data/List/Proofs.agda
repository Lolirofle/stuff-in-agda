module Data.List.Proofs where

import Lvl
open import Functional
open import Function.Names as Names using (_⊜_)
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
open import Structure.Function.Multi
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

private variable ℓ : Lvl.Level
private variable T A B : Type{ℓ}
private variable l l₁ l₂ : List(T)
private variable a b x : T
private variable n : ℕ
private variable f : A → B

module _ {ℓ₁ ℓ₂ : Lvl.Level} where
  List-induction : ∀{T : Type{ℓ₁}}{P : List(T) → Stmt{ℓ₂}} → P(∅) → (∀(x : T)(l : List(T)) → P(l) → P(x ⊰ l)) → (∀{l : List(T)} → P(l))
  List-induction base next {∅} = base
  List-induction base next {x ⊰ l} = next(x)(l)(List-induction base next {l})

module _ where
  instance
    [++]-identityₗ : Identityₗ{T₁ = List(T)} (_++_) ∅
    Identityₗ.proof([++]-identityₗ) = [≡]-intro

  [++]-identityᵣ-raw : Names.Identityᵣ (Functional.swap(foldᵣ{T = T}(_⊰_))) ∅
  [++]-identityᵣ-raw {x = ∅}     = [≡]-intro
  [++]-identityᵣ-raw {x = x ⊰ l} = [≡]-with(x ⊰_) ([++]-identityᵣ-raw {x = l})
  {-# REWRITE [++]-identityᵣ-raw #-}

  instance
    [++]-identityᵣ : Identityᵣ{T₁ = List(T)} (_++_) ∅
    Identityᵣ.proof([++]-identityᵣ) = [++]-identityᵣ-raw

  [++]-associativity-raw : Names.Associativity(_++_ {T = T})
  [++]-associativity-raw {x = l₀} {y = l₁} {z = l₂} = List-induction [≡]-intro next {l₀} where
    next : ∀(x)(l) → (((l ++ l₁) ++ l₂) ≡ (l ++ (l₁ ++ l₂))) → ((((x ⊰ l) ++ l₁) ++ l₂) ≡ ((x ⊰ l) ++ (l₁ ++ l₂)))
    next = \x _ → [≡]-with(x ⊰_)

  instance
    [++]-associativity : Associativity{T = List(T)} (_++_)
    Associativity.proof([++]-associativity {T}) {x}{y}{z} = [++]-associativity-raw {T} {x = x}{y = y}{z = z}

  postpend-of-prepend : (postpend{T = T} a (b ⊰ l) ≡ b ⊰ postpend a l)
  postpend-of-prepend = [≡]-intro

  reverse-postpend : (reverse{T = T}(postpend a l) ≡ a ⊰ reverse l)
  reverse-postpend {l = ∅}     = [≡]-intro
  reverse-postpend {l = x ⊰ l} = [≡]-with(postpend x) (reverse-postpend {l = l})

  prepend-[++] : (a ⊰ l ≡ singleton{T = T}(a) ++ l)
  prepend-[++] = [≡]-intro

  postpend-[++] : (postpend{T = T} a l ≡ l ++ singleton(a))
  postpend-[++] {l = ∅}     = [≡]-intro
  postpend-[++] {l = x ⊰ l} = [≡]-with(x ⊰_) (postpend-[++] {l = l})

  postpend-of-[++] : (postpend{T = T} a (l₁ ++ l₂) ≡ l₁ ++ postpend a l₂)
  postpend-of-[++] {a = a} {∅}      {l₂} = [≡]-intro
  postpend-of-[++] {a = a} {x ⊰ l₁} {l₂} = [≡]-with(x ⊰_) (postpend-of-[++] {a = a} {l₁} {l₂})

  map-postpend : (map f(postpend a l) ≡ postpend (f(a)) (map f(l)))
  map-postpend {f = f} {l = ∅}     = [≡]-intro
  map-postpend {f = f} {l = x ⊰ l} = [≡]-with (f(x) ⊰_) map-postpend

  reverse-[++] : (reverse(l₁ ++ l₂) ≡ reverse(l₂) ++ reverse(l₁))
  reverse-[++] {l₁ = ∅}      {l₂} = [≡]-intro
  reverse-[++] {l₁ = x ⊰ l₁} {l₂} = [≡]-with(postpend x) (reverse-[++] {l₁ = l₁} {l₂}) 🝖 postpend-of-[++] {l₁ = reverse l₂} {l₂ = reverse l₁}

  map-[++] : (map f(l₁ ++ l₂) ≡ map f(l₁) ++ map f(l₂))
  map-[++] {f = f} {l₁ = ∅} {∅} = [≡]-intro
  map-[++] {f = f} {l₁ = ∅} {x ⊰ l₂} = [≡]-intro
  map-[++] {f = f} {l₁ = x ⊰ l₁} {l₂} = [≡]-with(f(x) ⊰_) (map-[++] {f = f} {l₁ = l₁} {l₂})

  instance
    map-preserves-[++] : Preserving₂(map f)(_++_)(_++_)
    Preserving.proof map-preserves-[++] {l₁} {l₂} = map-[++] {l₁ = l₁} {l₂ = l₂}

  length-[∅] : (length(∅ {T = T}) ≡ 0)
  length-[∅] = [≡]-intro

  length-singleton : (length{T = T}(singleton(a)) ≡ 1)
  length-singleton = [≡]-intro

  instance
    length-preserves-prepend : Preserving₁(length)(a ⊰_)(𝐒)
    Preserving.proof (length-preserves-prepend {a = a}) {x} = [≡]-intro

  length-postpend : ((length ∘ postpend a) ⊜ (𝐒 ∘ length))
  length-postpend {x = ∅}     = [≡]-intro
  length-postpend {x = x ⊰ l} = [≡]-with(𝐒) (length-postpend {x = l})
  -- {-# REWRITE length-postpend #-}

  instance
    length-preserves-postpend : Preserving₁(length)(postpend a)(𝐒)
    Preserving.proof (length-preserves-postpend {a = a}) {x} = length-postpend {a = a}{x = x}

  length-[++] : (length{T = T}(l₁ ++ l₂) ≡ length(l₁) + length(l₂))
  length-[++] {T = T} {l₁ = l₁} {l₂} = List-induction base next {l₁} where
    base : length(∅ ++ l₂) ≡ length{T = T}(∅) + length(l₂)
    base = symmetry(_≡_) (identityₗ(_+_)(0))

    next : ∀(x)(l) → (length(l ++ l₂) ≡ length(l) + length(l₂)) → (length((x ⊰ l) ++ l₂) ≡ length(x ⊰ l) + length(l₂))
    next x l stmt = ([≡]-with(𝐒) stmt) 🝖 (symmetry(_≡_) ([+1]-commutativity {length(l)} {length(l₂)}))
    -- length(l++l₂) = length(l)+length(l₂) = length(l₂)+length(l)
    -- 𝐒(length(l++l₂)) = 𝐒(length(l₂)+length(l))  = length(l₂)+𝐒(length(l))  = 𝐒(length(l))+length(l₂)
    -- length(x ⊰ (l++l₂)) = length(x ⊰ l)+length(l₂)

  instance
    length-preserves-[++] : Preserving₂(length{T = T})(_++_)(_+_)
    Preserving.proof length-preserves-[++] {l₁} {l₂} = length-[++] {l₁ = l₁} {l₂ = l₂}

  length-reverse : ((length{T = T} ∘ reverse) ⊜ length)
  length-reverse {x = ∅}     = [≡]-intro
  length-reverse {x = x ⊰ l} = length-postpend{a = x}{x = reverse l} 🝖 [≡]-with(𝐒) (length-reverse {x = l})

  instance
    length-preserves-reverse : Preserving₁(length{T = T})(reverse)(id)
    Preserving.proof length-preserves-reverse {l} = length-reverse {x = l}

  length-repeat : ((length{T = T} ∘ repeat(a)) ⊜ id)
  length-repeat{T = T}{x = 𝟎}    = [≡]-intro
  length-repeat{T = T}{x = 𝐒(n)} = [≡]-with(𝐒) (length-repeat{T = T}{x = n})

  length-tail : ((length{T = T} ∘ tail) ⊜ (𝐏 ∘ length))
  length-tail{x = ∅}     = [≡]-intro
  length-tail{x = _ ⊰ l} = [≡]-intro

  instance
    length-preserves-tail : Preserving₁(length{T = T})(tail)(𝐏)
    Preserving.proof length-preserves-tail {l} = length-tail {x = l}

  length-map : ∀{f : A → B} → ((length ∘ map f) ⊜ length)
  length-map {f = f}{x = ∅}     = [≡]-intro
  length-map {f = f}{x = x ⊰ l} = [≡]-with(𝐒) (length-map {f = f}{x = l})

  instance
    length-preserves-map : Preserving₁(length{T = T})(map f)(id)
    Preserving.proof (length-preserves-map {f = f}) {l} = length-map {f = f}{x = l}

  instance
    [⊰]-cancellationₗ : Cancellationₗ {T₁ = T} (_⊰_)
    Cancellationₗ.proof([⊰]-cancellationₗ) = proof where
      proof : Names.Cancellationₗ(_⊰_)
      proof {x} {∅}      {∅}     _    = [≡]-intro
      proof {x} {∅}      {_ ⊰ _} ()
      proof {x} {_ ⊰ _}  {∅}     ()
      proof {x} {x1 ⊰ l1} {x2 ⊰ l2} p = [≡]-with(tail) p

  instance
    [⊰]-cancellationᵣ : Cancellationᵣ {T₁ = T} (_⊰_)
    Cancellationᵣ.proof([⊰]-cancellationᵣ) = proof where
      proof : Names.Cancellationᵣ(_⊰_)
      proof {∅}     [≡]-intro = [≡]-intro
      proof {x ⊰ l} p = injective(Right) ([≡]-with(firstElem) p)

  [⊰]-general-cancellationᵣ : ((a ⊰ l₁) ≡ (b ⊰ l₂)) → (l₁ ≡ l₂)
  [⊰]-general-cancellationᵣ p = [≡]-with(tail) p

  [⊰]-general-cancellationₗ : ((a ⊰ l₁) ≡ (b ⊰ l₂)) → (a ≡ b)
  [⊰]-general-cancellationₗ {l₁ = ∅}     {l₂ = ∅}      [≡]-intro = [≡]-intro
  [⊰]-general-cancellationₗ {l₁ = ∅}     {l₂ = _ ⊰ _} p with () ← [⊰]-general-cancellationᵣ p
  [⊰]-general-cancellationₗ {l₁ = _ ⊰ _} {l₂ = _ ⊰ _} p = injective(Right) ([≡]-with(firstElem) p)

  [∅][⊰]-unequal : (∅ ≢ x ⊰ l)
  [∅][⊰]-unequal ()

  [⊰]-unequal : (x ⊰ l ≢ l)
  [⊰]-unequal ()

  [∅]-postpend-unequal : (postpend x l ≢ ∅)
  [∅]-postpend-unequal {l = ∅}     ()
  [∅]-postpend-unequal {l = _ ⊰ _} ()

  postpend-unequal : (postpend x l ≢ l)
  postpend-unequal {l = ∅}     ()
  postpend-unequal {l = y ⊰ l} p = postpend-unequal {l = l} (cancellationₗ(_⊰_) p)

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
    [++]-cancellationₗ : Cancellationₗ(_++_ {T = T})
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

  length-[++^] : (length(l ++^ n) ≡ length(l) ⋅ n)
  length-[++^] {l = l}{𝟎}    = [≡]-intro
  length-[++^] {l = l}{𝐒(n)} =
    length-[++] {l₁ = l}{l ++^ n}
    🝖 [≡]-with(expr ↦ length(l) + expr) (length-[++^] {l = l}{n})

  length-isEmpty : (length(l) ≡ 0) ↔ (isEmpty(l) ≡ 𝑇)
  length-isEmpty {l = ∅}     = [↔]-intro (const [≡]-intro) (const [≡]-intro)
  length-isEmpty {l = x ⊰ L} = [↔]-intro (\()) (\())

multiply-singleton-repeat : (singleton(l) ++^ n ≡ repeat(l)(n))
multiply-singleton-repeat {l = l} {n = 𝟎}   = [≡]-intro
multiply-singleton-repeat {l = l} {n = 𝐒 n} = [≡]-with(l ⊰_) (multiply-singleton-repeat {l = l} {n = n})

reverse-involution-raw : Names.Involution(reverse{T = T})
reverse-involution-raw {x = ∅}     = [≡]-intro
reverse-involution-raw {x = x ⊰ l} = reverse-postpend {a = x}{l = reverse l} 🝖 [≡]-with(x ⊰_) (reverse-involution-raw {x = l})

instance
  reverse-involution : Involution(reverse{T = T})
  Involution.proof reverse-involution = reverse-involution-raw

first-0-length : (first(0)(l) ≡ ∅)
first-0-length {l = ∅}     = [≡]-intro
first-0-length {l = x ⊰ l} = [≡]-intro
{-# REWRITE first-0-length #-}

first-of-∅ : (first(n)(∅ {T = T}) ≡ ∅)
first-of-∅ {n = 𝟎}    = [≡]-intro
first-of-∅ {n = 𝐒(n)} = [≡]-intro

module _ {f g : A → B} where
  map-function-raw : (f ⊜ g) → (map f ⊜ map g)
  map-function-raw p {∅} = [≡]-intro
  map-function-raw p {x ⊰ l} rewrite p{x} = [≡]-with(g(x) ⊰_) (map-function-raw p {l})

module _ {f g : A → List(B)} where
  concatMap-function-raw : (f ⊜ g) → (concatMap f ⊜ concatMap g)
  concatMap-function-raw p {∅} = [≡]-intro
  concatMap-function-raw p {x ⊰ l} rewrite p{x} = [≡]-with(g(x) ++_) (concatMap-function-raw p {l})

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type{ℓ₁}} {B : Type{ℓ₂}} {C : Type{ℓ₃}} {f : B → C}{g : A → B} where
  map-preserves-[∘] : (map(f ∘ g) ⊜ (map f ∘ map g))
  map-preserves-[∘] {x = ∅}     = [≡]-intro
  map-preserves-[∘] {x = x ⊰ l} = [≡]-with(f(g(x)) ⊰_) (map-preserves-[∘] {x = l})

  -- map-preserves-[∘]-sym = \{l} → symmetry(_≡_) (map-preserves-[∘] {l})
  -- {-# REWRITE map-preserves-[∘]-sym #-}

map-preserves-id : (map id ⊜ id{T = List(T)})
map-preserves-id {x = ∅} = [≡]-intro
map-preserves-id {x = x ⊰ l} = [≡]-with(x ⊰_) (map-preserves-id {x = l})
{-# REWRITE map-preserves-id #-}

concatMap-[++] : (concatMap f (l₁ ++ l₂) ≡ (concatMap f l₁ ++ concatMap f l₂))
concatMap-[++] {f = f} {∅}      {l₂} = [≡]-intro
concatMap-[++] {f = f} {x ⊰ l₁} {l₂} = 
  (f(x) ++ concatMap f (l₁ ++ l₂))             🝖-[ [≡]-with(f(x) ++_) (concatMap-[++] {f = f} {l₁} {l₂}) ]
  (f(x) ++ (concatMap f l₁ ++ concatMap f l₂)) 🝖-[ associativity(_++_) {x = f(x)}{y = concatMap f l₁}{z = concatMap f l₂} ]-sym
  (f(x) ++ concatMap f l₁ ++ concatMap f l₂)   🝖-end

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type{ℓ₁}} {B : Type{ℓ₂}} {C : Type{ℓ₃}} {f : B → List(C)}{g : A → List(B)} where
  concatMap-[∘] : (concatMap(concatMap f ∘ g)) ⊜ (concatMap f ∘ concatMap g)
  concatMap-[∘] {∅}     = [≡]-intro
  concatMap-[∘] {x ⊰ l} =
    (concatMap(concatMap f ∘ g)) (x ⊰ l)                  🝖[ _≡_ ]-[]
    (concatMap f ∘ g) x ++ concatMap(concatMap f ∘ g) l   🝖-[ [≡]-with((concatMap f ∘ g) x ++_) (concatMap-[∘] {l}) ]
    (concatMap f ∘ g) x ++ (concatMap f ∘ concatMap g) l  🝖[ _≡_ ]-[]
    (concatMap f (g(x))) ++ (concatMap f (concatMap g l)) 🝖-[ concatMap-[++] {l₁ = g(x)}{l₂ = concatMap g l} ]-sym
    concatMap f (g(x) ++ concatMap g l)                   🝖[ _≡_ ]-[]
    concatMap f (concatMap g (x ⊰ l))                     🝖[ _≡_ ]-[]
    (concatMap f ∘ concatMap g) (x ⊰ l)                   🝖-end

concatMap-singleton : (concatMap{A = T} singleton) ⊜ id
concatMap-singleton {x = ∅} = [≡]-intro
concatMap-singleton {x = x ⊰ l} = [≡]-with(x ⊰_) (concatMap-singleton {x = l})
