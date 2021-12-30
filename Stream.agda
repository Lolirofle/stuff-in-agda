{-# OPTIONS --guardedness #-}

module Stream where

import      Lvl
open import Data.Boolean
open import Data.List as List using (List)
import      Data.List.Functions as List
import      Data.List.Proofs as List
import      Data.List.Equiv.Id as List
open import Functional
open import Function.Iteration
open import Function.Iteration.Proofs
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Numeral.Natural
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Relator
open import Type

private variable ℓ : Lvl.Level
private variable T A B : Type{ℓ}
private variable a x init : T
private variable f : A → B
private variable n : ℕ

-- A countably infinite list
record Stream (T : Type{ℓ}) : Type{ℓ} where
  coinductive
  field
    head : T
    tail : Stream(T)
open Stream

module _ where
  -- The n:th element of a stream.
  -- Example: index(2)(0,1,2,…) = 2
  index : Stream(T) → ℕ → T
  index(l)(𝟎)    = head(l)
  index(l)(𝐒(n)) = index(tail(l))(n)

  -- The constant stream, consisting of a single element repeated.
  -- Example: repeat(x) = (x,x,x,..)
  repeat : T → Stream(T)
  head(repeat(x)) = x
  tail(repeat(x)) = repeat(x)

  -- The stream consisting of a list repeated (concatenated infinite many times).
  -- Example: loop(1,2,3) = (1,2,3 , 1,2,3 , 1,2,3 , …)
  loop : (l : List(T)) → (l ≢ List.∅) → Stream(T)
  loop List.∅       p with () ← p [≡]-intro
  head (loop (x List.⊰ l) p) = x
  tail (loop (x List.⊰ l) p) = loop (List.postpend x l) List.[∅]-postpend-unequal

  -- The stream of two interleaved streams.
  -- Example: interleave₂(1,2,3,‥)(a,b,c,…) = (1,a , 2,b , 3,c , …)
  interleave₂ : Stream(T) -> Stream(T) -> Stream(T)
  head(interleave₂(a)(b)) = head(a)
  tail(interleave₂(a)(b)) = interleave₂(b)(tail a)

  -- A stream which skips the first n number of elements from the specified stream.
  -- From the stream of (index 0 l , index 1 l , index 2 l , ..), the stream of (index n l , index (n+1) l , index (n+2) l , ..)
  -- Example: skip(2)(1,2,3,4,…) = (3,4,…)
  skip : ℕ → Stream(T) -> Stream(T)
  head(skip 𝟎      l) = head(l)
  tail(skip 𝟎      l) = tail(l)
  head(skip (𝐒(n)) l) = head(skip n (tail(l)))
  tail(skip (𝐒(n)) l) = tail(skip n (tail(l)))

  -- From the stream of (index 0 l , index 1 l , index 2 l , ..), the stream of (index 0 l , index n l , index (2⋅n) l , ..)
  -- Example: takeMultiples(3)(0,1,2,…) = (0,3,6,…)
  takeMultiples : ℕ → Stream(T) -> Stream(T)
  head(takeMultiples _ l) = head(l)
  tail(takeMultiples n l) = takeMultiples n ((tail ^ n) l)

  -- From the stream of (a,b,c,..), the stream of (x,a,b,c,..)
  _⊰_ : T → Stream(T) -> Stream(T)
  head(x ⊰ _) = x
  tail(_ ⊰ l) = l

  -- Stream of (init , f(init) , f(f(init)) , ..)
  iterated : T -> (T → T) → Stream(T)
  head(iterated init _) = init
  tail(iterated init f) = iterated (f(init)) f

  -- List from the initial part of the stream
  take : ℕ → Stream(T) → List(T)
  take(𝟎)   (l) = List.∅
  take(𝐒(n))(l) = head(l) List.⊰ take(n)(tail(l))

  -- Example: indexIntervals(0,0,2,0,1,2,…)(0,1,2,3,…) = (0,0,2,2,3,5,…)
  indexIntervals : Stream(ℕ) → Stream(T) → Stream(T)
  head (indexIntervals i l) = index l (head i)
  tail (indexIntervals i l) = indexIntervals (tail i) (skip (head i) l)

module _ where
  -- From the stream of (a,b,c,..), the stream of (f(a),f(b),f(c),..)
  map : (A → B) → Stream(A) → Stream(B)
  head(map f(l)) = f(head(l))
  tail(map f(l)) = map f(tail(l))

{- TODO: May not terminate. For example when P = const 𝐹
module _ {ℓ} {A : Type{ℓ}} where
  filter : (A → Bool) → Stream(A) → Stream(A)
  head(filter p(l)) with p(head(l))
  ... | 𝑇 = head(l)
  ... | 𝐹 = head(filter p(tail(l)))
  tail(filter p(l)) = filter p(tail(l))
-}

module _ where
  data _∈_ {T : Type{ℓ}} : T → Stream(T) → Stmt{ℓ} where
    [∈]-head : ∀{l}   → (head(l) ∈ l)
    [∈]-tail : ∀{a l} → (a ∈ tail(l)) → (a ∈ l)

  private variable l : Stream(T)

  index-of-[∈] : (x ∈ l) → ℕ
  index-of-[∈] [∈]-head     = 𝟎
  index-of-[∈] ([∈]-tail p) = 𝐒(index-of-[∈] p)

  index-of-[∈]-correctness : ∀{p : (x ∈ l)} → (index l (index-of-[∈] p) ≡ x)
  index-of-[∈]-correctness {x = .(head l)} {l} {[∈]-head}   = [≡]-intro
  index-of-[∈]-correctness {x = x}         {l} {[∈]-tail p} = index-of-[∈]-correctness {x = x} {tail l} {p}

  _⊆_ : Stream(T) → Stream(T) → Stmt
  _⊆_ l₁ l₂ = ∀{a} → (a ∈ l₁) → (a ∈ l₂)

  [∈]-tails : ((tail ^ n)(l) ⊆ l)
  [∈]-tails {n = 𝟎}   {l = l} {a} tailn = tailn
  [∈]-tails {n = 𝐒 n} {l = l} {a} tailn = [∈]-tail ([∈]-tails {n = n} {l = tail l} {a} (substitute₁ₗ(a ∈_) ([^]-inner-value {f = tail}{x = l}{n}) tailn))

  [∈]-head-tail : (head(tail(l)) ∈ l)
  [∈]-head-tail = [∈]-tail ([∈]-head)

  [∈]-head-tails-membership : (head((tail ^ n)(l)) ∈ l)
  [∈]-head-tails-membership{𝟎}       = [∈]-head
  [∈]-head-tails-membership{𝐒(n)}{l} = [∈]-tails {n = n} ([∈]-head-tail)

  [∈]-disjunction : (x ∈ l) → ((x ≡ head(l)) ∨ (x ∈ tail(l)))
  [∈]-disjunction ([∈]-head)       = [∨]-introₗ [≡]-intro
  [∈]-disjunction ([∈]-tail proof) = [∨]-introᵣ proof

  [∈]-index : (index l n ∈ l)
  [∈]-index {n = 𝟎}    = [∈]-head
  [∈]-index {n = 𝐒(n)} = [∈]-tail ([∈]-index {n = n})

  repeat-[∈] : (x ∈ repeat(a)) ↔ (x ≡ a)
  repeat-[∈] {x = x}{a = a} = [↔]-intro left right where
    left : (x ∈ repeat(a)) ← (x ≡ a)
    left ([≡]-intro) = [∈]-head

    right : (x ∈ repeat(a)) → (x ≡ a)
    right ([∈]-head)       = [≡]-intro
    right ([∈]-tail proof) = right(proof)

  map-[∈] : (x ∈ l) → (f(x) ∈ map f(l))
  map-[∈]         ([∈]-head)       = [∈]-head
  map-[∈] {l = l} ([∈]-tail proof) = [∈]-tail (map-[∈] {l = tail l} (proof))

  [⊰][∈] : (a ∈ (x ⊰ l)) ↔ ((x ≡ a) ∨ (a ∈ l))
  [⊰][∈] {a = a}{x = x}{l = l} = [↔]-intro ll rr where
    ll : (a ∈ (x ⊰ l)) ← ((x ≡ a) ∨ (a ∈ l))
    ll ([∨]-introₗ ([≡]-intro)) = [∈]-head
    ll ([∨]-introᵣ (proof))     = [∈]-tail (proof)

    rr : (a ∈ (x ⊰ l)) → ((x ≡ a) ∨ (a ∈ l))
    rr ([∈]-head)         = [∨]-introₗ ([≡]-intro)
    rr ([∈]-tail (proof)) = [∨]-introᵣ (proof)

  iterated-init-[∈] : (init ∈ iterated(init)(f))
  iterated-init-[∈] = [∈]-head

  iterated-next-[∈] : (x ∈ iterated(init)(f)) → (f(x) ∈ iterated(init)(f))
  iterated-next-[∈] ([∈]-head)       = [∈]-tail ([∈]-head)
  iterated-next-[∈] ([∈]-tail proof) = [∈]-tail (iterated-next-[∈] (proof))
  -- First:
  --   head(iterated(init)(f)) ∈ iterated(init)(f)
  --   init ∈ iterated(init)(f)
  --   ...
  -- Second:
  --   x ∈ tail(iterated(init)(f))
  --   x ∈ iterated (f(init)) f
  --   ...

  iterated-[∈] : ((f ^ n)(init) ∈ iterated(init)(f))
  iterated-[∈] {n = 𝟎}   = iterated-init-[∈]
  iterated-[∈] {n = 𝐒 n} = iterated-next-[∈] (iterated-[∈] {n = n})

-- Stream of (0,1,2,3,..)
[ℕ]-stream : Stream(ℕ)
[ℕ]-stream = iterated(𝟎)(𝐒)

[ℕ]-stream-[∈] : (n ∈ [ℕ]-stream)
[ℕ]-stream-[∈]{𝟎}    = [∈]-head
[ℕ]-stream-[∈]{𝐒(n)} = iterated-next-[∈]([ℕ]-stream-[∈]{n})

-- Stream of (f(0),f(1),f(2),f(3),..)
[ℕ]-function-stream : (ℕ → T) → Stream(T)
[ℕ]-function-stream f = map f([ℕ]-stream)

module _ {ℓ} {T : Type{ℓ}} where
  open import Logic.Predicate
  open import Logic.Predicate.Theorems
  open import Structure.Function.Domain
  open import Type.Size.Countable

  -- This provides another way of proving that a type is countable.
  -- The method is: If a stream can enumerate every object of a certain type, then it is countable.
  countable-equivalence : ∃(l ↦ ∀{x : T} → (x ∈ l)) ↔ Countable(T)
  countable-equivalence = [↔]-intro left right where
    left : ∃(l ↦ ∀{x : T} → (x ∈ l)) ← Countable(T)
    ∃.witness (left ([∃]-intro f ⦃ intro proof ⦄)) = [ℕ]-function-stream f
    ∃.proof   (left ([∃]-intro f ⦃ intro proof ⦄)) {x} with proof{x}
    ... | [∃]-intro n ⦃ [≡]-intro ⦄ = map-[∈] [ℕ]-stream-[∈]

    right : ∃(l ↦ ∀{x : T} → (x ∈ l)) → Countable(T)
    ∃.witness (right ([∃]-intro l ⦃ p ⦄)) = index l
    ∃.witness (Surjective.proof (∃.proof (right ([∃]-intro l ⦃ p ⦄))) {x}) = index-of-[∈] (p{x})
    ∃.proof   (Surjective.proof (∃.proof (right ([∃]-intro l ⦃ p ⦄))) {x}) = index-of-[∈]-correctness {p = p}
