module Data.List.Proofs.Length where

import Lvl
open import Functional
open import Function.Names as Names using (_⊜_)
open import Data.Boolean
open import Data.List as List
open import Data.List.Functions
open import Logic
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function.Multi
open import Structure.Operator.Properties
open import Structure.Operator
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable T A B : Type{ℓ}
private variable l l₁ l₂ : List(T)
private variable a b x : T
private variable n : ℕ
private variable f : A → B
private variable P : List(T) → Stmt{ℓ}

-- TODO: Almost all of these can use Preserving instead

length-[∅] : (length(∅ {T = T}) ≡ 0)
length-[∅] = [≡]-intro

length-singleton : (length{T = T}(singleton(a)) ≡ 1)
length-singleton = [≡]-intro

instance
  length-preserves-prepend : Preserving₁(length)(a ⊰_)(𝐒)
  Preserving.proof (length-preserves-prepend {a = a}) {x} = [≡]-intro

length-postpend : ((length ∘ postpend a) ⊜ (𝐒 ∘ length))
length-postpend {x = l} = List.elim [≡]-intro (\x l → [≡]-with(𝐒) {length(postpend _ l)}{𝐒(length l)}) l

instance
  length-preserves-postpend : Preserving₁(length)(postpend a)(𝐒)
  Preserving.proof (length-preserves-postpend {a = a}) {x} = length-postpend {a = a}{x = x}

length-[++] : (length{T = T}(l₁ ++ l₂) ≡ length(l₁) + length(l₂))
length-[++] {T = T} {l₁ = l₁} {l₂} = List.elim base next l₁ where
  base : length(∅ ++ l₂) ≡ length{T = T}(∅) + length(l₂)
  base = symmetry(_≡_) (identityₗ(_+_)(0))

  next : ∀(x)(l) → (length(l ++ l₂) ≡ length(l) + length(l₂)) → (length((x ⊰ l) ++ l₂) ≡ length(x ⊰ l) + length(l₂))
  next x l stmt =
    length((x ⊰ l) ++ l₂)      🝖[ _≡_ ]-[]
    length(x ⊰ (l ++ l₂))      🝖[ _≡_ ]-[]
    𝐒(length(l ++ l₂))         🝖[ _≡_ ]-[ [≡]-with(𝐒) stmt ]
    𝐒(length(l) + length(l₂))  🝖[ _≡_ ]-[ [+]-stepₗ {length(l)} {length(l₂)} ]
    𝐒(length(l)) + length(l₂)  🝖[ _≡_ ]-[]
    length(x ⊰ l) + length(l₂) 🝖-end

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

length-foldᵣ : ∀{init}{f}{g} → (∀{x}{l} → (length(f x l) ≡ g x (length l))) → (length{T = T}(foldᵣ f init l) ≡ foldᵣ g (length init) l)
length-foldᵣ {l = ∅}                    _ = [≡]-intro
length-foldᵣ {l = x ⊰ l} {init} {f} {g} p =
  length(foldᵣ f init (x ⊰ l))    🝖[ _≡_ ]-[]
  length(f(x) (foldᵣ f init l))   🝖[ _≡_ ]-[ p ]
  g(x) (length(foldᵣ f init l))   🝖[ _≡_ ]-[ [≡]-with(g(x)) (length-foldᵣ {l = l} {init} {f} {g} p) ]
  g(x) (foldᵣ g (length init) l)  🝖[ _≡_ ]-[]
  foldᵣ g (length init) (x ⊰ l)   🝖-end

length-concatMap : ∀{f} → (length{T = T}(concatMap f l) ≡ foldᵣ((_+_) ∘ length ∘ f) 𝟎 l)
length-concatMap {l = l} {f} = length-foldᵣ{l = l}{init = ∅}{f = (_++_) ∘ f} \{x l} → length-[++] {l₁ = f(x)}{l₂ = l}

length-accumulateIterate₀ : ∀{n}{f}{init : T} → (length(accumulateIterate₀ n f init) ≡ n)
length-accumulateIterate₀ {n = 𝟎}      = [≡]-intro
length-accumulateIterate₀ {n = 𝐒 n}{f} = [≡]-with(𝐒) (length-accumulateIterate₀ {n = n}{f})

length-[++^] : (length(l ++^ n) ≡ length(l) ⋅ n)
length-[++^] {l = l}{𝟎}    = [≡]-intro
length-[++^] {l = l}{𝐒(n)} =
  length-[++] {l₁ = l}{l ++^ n}
  🝖 [≡]-with(expr ↦ length(l) + expr) (length-[++^] {l = l}{n})

length-isEmpty : (length(l) ≡ 0) ↔ (isEmpty(l) ≡ 𝑇)
length-isEmpty {l = ∅}     = [↔]-intro (const [≡]-intro) (const [≡]-intro)
length-isEmpty {l = x ⊰ L} = [↔]-intro (\()) (\())
