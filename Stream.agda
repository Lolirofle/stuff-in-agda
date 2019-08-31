module Stream where

import      Lvl
open import Functional
open import Functional.Repeat
open import Data.List using (List)
open import Logic
open import Logic.Propositional
open import Numeral.Natural
open import Relator.Equals
open import Type

-- A countably infinite list
record Stream {ℓ} (T : Type{ℓ}) : Type{ℓ} where
  coinductive
  field
    head : T
    tail : Stream(T)
open Stream

module _ {ℓ} {T : Type{ℓ}} where
  index : Stream(T) → ℕ -> T
  index(l)(𝟎)    = head(l)
  index(l)(𝐒(n)) = index(tail(l))(n)

  -- Stream of (x,x,x,..)
  repeat : T -> Stream(T)
  head(repeat(x)) = x
  tail(repeat(x)) = repeat(x)

  interleave₂ : Stream(T) -> Stream(T) -> Stream(T)
  head(interleave₂(a)(b)) = head(a)
  tail(interleave₂(a)(b)) = interleave₂(b)(a)

  -- From the stream of (index 0 l , index 1 l , index 2 l , ..), the stream of (index n l , index (n+1) l , index (n+2) l , ..)
  skip : ℕ → Stream(T) -> Stream(T)
  head(skip 𝟎      l) = head(l)
  tail(skip 𝟎      l) = tail(l)
  head(skip (𝐒(n)) l) = head(skip n (tail(l)))
  tail(skip (𝐒(n)) l) = tail(skip n (tail(l)))

  -- From the stream of (index 0 l , index 1 l , index 2 l , ..), the stream of (index 0 l , index n l , index (2⋅n) l , ..)
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

module _ {ℓ₁ ℓ₂} {A : Type{ℓ₁}} {B : Type{ℓ₂}} where
  -- From the stream of (a,b,c,..), the stream of (f(a),f(b),f(c),..)
  map : (A → B) → Stream(A) -> Stream(B)
  head(map f(l)) = f(head(l))
  tail(map f(l)) = map f(tail(l))

module _ {ℓ} {T : Type{ℓ}} where
  data _∈_ : T → Stream(T) → Stmt{ℓ} where
    instance
      [∈]-head : ∀{l}   → (head(l) ∈ l)
      [∈]-tail : ∀{a l} → (a ∈ tail(l)) → (a ∈ l)

  [∈]-head-tail : ∀{l} → (head(tail(l)) ∈ l)
  [∈]-head-tail = [∈]-tail ([∈]-head)

  -- head-tails-inclusion : ∀{n}{l} → (head((tail ^ n)(l)) ∈ l)
  -- head-tails-inclusion{𝟎}    = [∈]-head
  -- head-tails-inclusion{𝐒(n)} = [∈]-tail (head-tails-inclusion{n})

  [∈]-disjunction : ∀{x}{l} → (x ∈ l) → ((x ≡ head(l)) ∨ (x ∈ tail(l)))
  [∈]-disjunction ([∈]-head)       = [∨]-introₗ [≡]-intro
  [∈]-disjunction ([∈]-tail proof) = [∨]-introᵣ proof

  -- [∈]-index : ∀{n}{l} → (index(n)(l) ∈ l)
  -- [∈]-index {𝟎}    = [∈]-head
  -- [∈]-index {𝐒(n)} = [∈]-head-tails

  repeat-[∈] : ∀{a}{x} → (x ∈ repeat(a)) ↔ (x ≡ a)
  repeat-[∈] {a}{x} = [↔]-intro l r where
    l : (x ∈ repeat(a)) ← (x ≡ a)
    l ([≡]-intro) = [∈]-head

    r : (x ∈ repeat(a)) → (x ≡ a)
    r ([∈]-head)       = [≡]-intro
    r ([∈]-tail proof) = r(proof)

  map-[∈] : ∀{x}{l} → (x ∈ l) → ∀{f} → (f(x) ∈ map f(l))
  map-[∈] ([∈]-head)       = [∈]-head
  map-[∈] ([∈]-tail proof) = [∈]-tail (map-[∈] (proof))

  [⊰][∈] : ∀{a}{x}{l} → (a ∈ (x ⊰ l)) ↔ ((x ≡ a) ∨ (a ∈ l))
  [⊰][∈] {a}{x}{l} = [↔]-intro ll rr where
    ll : (a ∈ (x ⊰ l)) ← ((x ≡ a) ∨ (a ∈ l))
    ll ([∨]-introₗ ([≡]-intro)) = [∈]-head
    ll ([∨]-introᵣ (proof))     = [∈]-tail (proof)

    rr : (a ∈ (x ⊰ l)) → ((x ≡ a) ∨ (a ∈ l))
    rr ([∈]-head)         = [∨]-introₗ ([≡]-intro)
    rr ([∈]-tail (proof)) = [∨]-introᵣ (proof)

  iterated-init-[∈] : ∀{init}{f} → (init ∈ iterated(init)(f))
  iterated-init-[∈] = [∈]-head

  iterated-next-[∈] : ∀{x}{init}{f} → (x ∈ iterated(init)(f)) → (f(x) ∈ iterated(init)(f))
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

-- Stream of (0,1,2,3,..)
[ℕ]-stream : Stream(ℕ)
[ℕ]-stream = iterated(𝟎)(𝐒)

{-
[ℕ]-stream-includes-[0] : (0 ∈ [ℕ]-stream)
[ℕ]-stream-includes-[0] = [∈]-head

[ℕ]-stream-includes-[1] : (1 ∈ [ℕ]-stream)
[ℕ]-stream-includes-[1] = [∈]-tail([∈]-head)

[ℕ]-stream-includes-[2] : (2 ∈ [ℕ]-stream)
[ℕ]-stream-includes-[2] = [∈]-tail([∈]-tail([∈]-head))
-}

[ℕ]-stream-[∈] : ∀{n : ℕ} → (n ∈ [ℕ]-stream)
[ℕ]-stream-[∈]{𝟎}    = [∈]-head
[ℕ]-stream-[∈]{𝐒(n)} = iterated-next-[∈]([ℕ]-stream-[∈]{n})
