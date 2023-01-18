module Data.List.Proofs.Length where

import Lvl
open import Function.Names using (_⊜_ ; _⊜₂_)
open import Functional
open import Data.Boolean
open import Data.List as List
open import Data.List.Functions
open import Logic
open import Logic.Propositional
open import Numeral.Finite
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function
open import Structure.Function.Multi
open import Structure.Operator.Properties
open import Structure.Operator
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable T A B : Type{ℓ}
private variable l l₁ l₂ : List(T)
private variable a b x init n : T
private variable f g : A → B
private variable P : List(T) → Stmt{ℓ}

-- TODO: Almost all of these can use Preserving instead

length-[∅] : length(∅ {T = T}) ≡ 0
length-[∅] = [≡]-intro

length-singleton : length{T = T}(singleton(a)) ≡ 1
length-singleton = [≡]-intro

instance
  length-preserves-prepend : Preserving₁(length)(a ⊰_)(𝐒)
  Preserving.proof (length-preserves-prepend {a = a}) {x} = [≡]-intro
 
instance
  length-preserves-postpend : Preserving₁(length)(postpend a)(𝐒)
  length-preserves-postpend {a = a} = intro \{l} → List.elim _ [≡]-intro (\x l → congruence₁(𝐒) {length(postpend _ l)}{𝐒(length l)}) l

length-[++] : (length{T = T}(l₁ ++ l₂) ≡ length(l₁) + length(l₂))
length-[++] {T = T} {l₁ = l₁} {l₂} = List.elim _ base next l₁ where
  base : length(∅ ++ l₂) ≡ length{T = T}(∅) + length(l₂)
  base = symmetry(_≡_) (identityₗ(_+_)(0))

  next : ∀(x)(l) → (length(l ++ l₂) ≡ length(l) + length(l₂)) → (length((x ⊰ l) ++ l₂) ≡ length(x ⊰ l) + length(l₂))
  next x l stmt =
    length((x ⊰ l) ++ l₂)      🝖[ _≡_ ]-[]
    length(x ⊰ (l ++ l₂))      🝖[ _≡_ ]-[]
    𝐒(length(l ++ l₂))         🝖[ _≡_ ]-[ congruence₁(𝐒) stmt ]
    𝐒(length(l) + length(l₂))  🝖[ _≡_ ]-[ [+]-stepₗ {length(l)} {length(l₂)} ]
    𝐒(length(l)) + length(l₂)  🝖[ _≡_ ]-[]
    length(x ⊰ l) + length(l₂) 🝖-end

instance
  length-preserves-[++] : Preserving₂(length{T = T})(_++_)(_+_)
  Preserving.proof length-preserves-[++] {l₁} {l₂} = length-[++] {l₁ = l₁} {l₂ = l₂}

instance
  length-preserves-reverse : Preserving₁(length{T = T})(reverse.byPostpend)(id)
  length-preserves-reverse = intro \{l} → p{l} where
    p : (length ∘ reverse.byPostpend) ⊜ length
    p{∅}     = [≡]-intro
    p{x ⊰ l} =
      length(reverse.byPostpend(x ⊰ l))         🝖[ _≡_ ]-[]
      length(postpend x (reverse.byPostpend l)) 🝖[ _≡_ ]-[ preserving₁(length)(postpend x)(𝐒) {reverse.byPostpend l} ]
      𝐒(length(reverse.byPostpend l))           🝖[ _≡_ ]-[ congruence₁(𝐒) (p{l}) ]
      𝐒(length l)                               🝖[ _≡_ ]-[]
      length(x ⊰ l)                             🝖-end
    -- length-postpend{a = x}{x = reverse l} 🝖 congruence₁(𝐒) (length-reverse {x = l})

length-repeat : (length{T = T} ∘ repeat(a)) ⊜ id
length-repeat{T = T}{x = 𝟎}    = [≡]-intro
length-repeat{T = T}{x = 𝐒(n)} = congruence₁(𝐒) (length-repeat{T = T}{x = n})

instance
  length-preserves-tail : Preserving₁(length{T = T})(tail)(𝐏)
  length-preserves-tail = intro \{l} → p{l} where
    p : ((length ∘ tail) ⊜ (𝐏 ∘ length))
    p{∅}     = [≡]-intro
    p{_ ⊰ _} = [≡]-intro

length-map : ((length ∘ map f) ⊜ length)
length-map {f = f}{x = ∅}     = [≡]-intro
length-map {f = f}{x = x ⊰ l} = congruence₁(𝐒) (length-map {f = f}{x = l})

instance
  length-preserves-map : Preserving₁(length{T = T})(map f)(id)
  Preserving.proof (length-preserves-map {f = f}) {l} = length-map {f = f}{x = l}

length-foldᵣ : (∀{x} → (length ∘ f x ⊜ g x ∘ length)) → ((length ∘₂ foldᵣ f) ⊜₂ (foldᵣ g ∘ length))
length-foldᵣ                             _ {_}   {∅}     = [≡]-intro
length-foldᵣ {f = f}{g = g}              p {init}{x ⊰ l} =
  length(foldᵣ f init (x ⊰ l))    🝖[ _≡_ ]-[]
  length(f(x) (foldᵣ f init l))   🝖[ _≡_ ]-[ p ]
  g(x) (length(foldᵣ f init l))   🝖[ _≡_ ]-[ congruence₁(g(x)) (length-foldᵣ {f = f}{g = g} p {init}{l}) ]
  g(x) (foldᵣ g (length init) l)  🝖[ _≡_ ]-[]
  foldᵣ g (length init) (x ⊰ l)   🝖-end

length-concatMap : (length(concatMap f l) ≡ foldᵣ((_+_) ∘ length ∘ f) 𝟎 l)
length-concatMap {f = f}{l = l} = length-foldᵣ{f = (_++_) ∘ f} (\{x l} → length-[++] {l₁ = f(x)}{l₂ = l}) {∅}{l}

length-accumulateIterate₀ : (length(accumulateIterate₀ n f init) ≡ n)
length-accumulateIterate₀ {n = 𝟎}      = [≡]-intro
length-accumulateIterate₀ {n = 𝐒 n}{f} = congruence₁(𝐒) (length-accumulateIterate₀ {n = n}{f})

length-[++^] : (length(l ++^ n) ≡ length(l) ⋅ n)
length-[++^] {l = l}{𝟎}    = [≡]-intro
length-[++^] {l = l}{𝐒(n)} =
  length-[++] {l₁ = l}{l ++^ n}
  🝖 congruence₁(expr ↦ length(l) + expr) (length-[++^] {l = l}{n})

length-isEmpty : (length(l) ≡ 0) ↔ (isEmpty(l) ≡ 𝑇)
length-isEmpty {l = ∅}     = [↔]-intro (const [≡]-intro) (const [≡]-intro)
length-isEmpty {l = x ⊰ L} = [↔]-intro (\()) (\())

instance
  length-preserves-insert : Preserving₁(length)(insert n x)(𝐒)
  Preserving.proof (length-preserves-insert {n = n}) = proof{n = n} where
    proof : ∀{n} → (length(insert n x l) ≡ 𝐒(length l))
    proof         {l = _}     {n = 𝟎}   = [≡]-intro
    proof         {l = ∅}     {n = 𝐒 n} = [≡]-intro
    proof {x = x} {l = y ⊰ l} {n = 𝐒 n} rewrite proof {x = x} {l = l} {n = n} = [≡]-intro

length-insertIn : length(insertIn x l n) ≡ 𝐒(length l)
length-insertIn         {l = _}     {n = 𝟎}   = [≡]-intro
length-insertIn {x = x} {l = y ⊰ l} {n = 𝐒 n} rewrite length-insertIn {x = x} {l = l} {n = n} = [≡]-intro
