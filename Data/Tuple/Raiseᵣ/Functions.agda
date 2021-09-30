module Data.Tuple.Raiseᵣ.Functions where

import      Lvl
open import Data hiding (empty)
open import Data.Option as Option using (Option)
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Data.Tuple.Raiseᵣ
open import Functional as Fn using (id ; const ; apply ; swap ; _∘₂_)
open import Functional.Dependent using (_∘_)
open import Numeral.Natural
open import Numeral.Natural.Oper using (_+_ ; _⋅_)
open import Numeral.Natural.Oper.Proofs.Rewrite
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Order
open import Numeral.Finite
open import Syntax.Function
open import Syntax.Number
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T A B C A₁ A₂ : Type{ℓ}
private variable n n₁ n₂ : ℕ

-------------------------------------------------------------------------------
-- Primitives

-- Prepends an element to a tuple.
-- Example: a ⊰ (b,c) = (a,b,c)
_⊰_ : let _ = n in T → (T ^ n) → (T ^ 𝐒(n))
_⊰_ {𝟎}    = const
_⊰_ {𝐒(n)} = _,_
prepend = _⊰_

elimDep : ∀{ℓ : ∀(n) → (T ^ n) → Lvl.Level} → (P : ∀(n) → (l : (T ^ n)) → Type{ℓ n l}) → P(𝟎)(<>) → (∀(x) → P(𝐒(𝟎))(x)) → (∀{n}(x)(l) → P(𝐒(n))(l) → P(𝐒(𝐒(n)))(x , l)) → (∀{n}(l) → P(n)(l))
elimDep _ p₀ _  _  {0}       <>      = p₀
elimDep _ _  p₁ _  {1}       x       = p₁ x
elimDep P p₀ p₁ p₊ {𝐒(𝐒(n))} (x , l) = p₊ x l (elimDep P p₀ p₁ p₊ {𝐒(n)} l)

-------------------------------------------------------------------------------
-- Derivations from the primitives

elim : (P : ∀(n) → (T ^ n) → Type{ℓ}) → P(𝟎)(<>) → (∀(x) → P(𝐒(𝟎))(x)) → (∀{n}(x)(l) → P(𝐒(n))(l) → P(𝐒(𝐒(n)))(x , l)) → (∀{n}(l) → P(n)(l))
elim = elimDep

elim₊ : (P : ∀(n) → (T ^ 𝐒(n)) → Type{ℓ}) → (∀(x) → P(𝟎)(x)) → (∀{n}(x)(l) → P(n)(l) → P(𝐒(n))(x , l)) → (∀{n}(l) → P(n)(l))
elim₊{T = T} P p₁ p₊ {n} l = elim P₀ <> p₁ p₊ {𝐒(n)} l where
  P₀ : ∀(n : ℕ) → (T ^ n) → Type
  P₀ 𝟎     = const Unit
  P₀ (𝐒 n) = P(n)

elimIndepOp : (P : ℕ → Type{ℓ}) → P(𝟎) → (∀{n} → T → P(n) → P(𝐒(n))) → (∀{n} → (T ^ n) → P(n))
elimIndepOp P p₀ p₊ = elim(const ∘ P) p₀ (apply p₀ ∘ p₊) (const ∘ p₊)

-- Example: reduceᵣ(_▫_) (a,b,c,d) = a ▫ (b ▫ (c ▫ d))
-- Alternative implementation:
--   reduceᵣ {𝟎}    (_▫_) x        = x
--   reduceᵣ {𝐒(n)} (_▫_) (x , xs) = x ▫ reduceᵣ {n} (_▫_) xs
reduceᵣ : let _ = n in (T → T → T) → (T ^ 𝐒(n)) → T
reduceᵣ(_▫_) = elim₊ _ id (const ∘ (_▫_))

-- Example: foldᵣ(_▫_) def (a,b,c,d) = a ▫ (b ▫ (c ▫ (d ▫ def)))
-- Alternative implementation:
--   foldᵣ {0}       (_▫_) def _        = def
--   foldᵣ {1}       (_▫_) def x        = x ▫ def
--   foldᵣ {𝐒(𝐒(n))} (_▫_) def (x , xs) = x ▫ foldᵣ {𝐒(n)} (_▫_) def xs
foldᵣ : let _ = n in (A → B → B) → B → (A ^ n) → B
foldᵣ(_▫_) id = elimIndepOp _ id (_▫_)

-- Example: reduceOrᵣ(_▫_) def (a,b,c,d) = a ▫ (b ▫ (c ▫ d))
-- Alternative implementation:
--   reduceOrᵣ {0}       (_▫_) def _        = def
--   reduceOrᵣ {1}       (_▫_) def x        = x
--   reduceOrᵣ {𝐒(𝐒(n))} (_▫_) def (x , xs) = x ▫ reduceOrᵣ {𝐒(n)} (_▫_) def xs
reduceOrᵣ : let _ = n in (A → A → A) → A → (A ^ n) → A
reduceOrᵣ{n} (_▫_) def = elim _ def id (const ∘ (_▫_)) {n}

-- Postpends an element to a tuple.
-- Example: postpend c (a,b) = (a,b,c)
-- Alternative implementation:
--   postpend {0}       a _       = a
--   postpend {1}       a x       = (x , a)
--   postpend {𝐒(𝐒(n))} a (x , l) = (x , postpend {n = 𝐒(n)} a l)
postpend : let _ = n in T → (T ^ n) → (T ^ (𝐒(n)))
postpend{T = T} a = elimIndepOp((T ^_) ∘ 𝐒) a prepend

-- Example: map f(a,b,c,d) = (f(a),f(b),f(c),f(d))
-- Alternative implementation:
--   map {0}       f _ = <>
--   map {1}       f single        = f(single)
--   map {𝐒(𝐒(n))} f (init , rest) = (f(init) , map{𝐒(n)} f rest)
map : let _ = n in (A → B) → ((A ^ n) → (B ^ n))
map f = elimIndepOp(_ ^_) <> (prepend ∘ f)

-- Example: foldₗ(_▫_) def (a,b,c,d) = (((def ▫ a) ▫ b) ▫ c) ▫ d
-- Alternative implementation:
--   foldₗ {0}       (_▫_) def _        = def
--   foldₗ {1}       (_▫_) def x        = def ▫ x
--   foldₗ {𝐒(𝐒(n))} (_▫_) def (x , xs) = foldₗ {𝐒(n)} (_▫_) (def ▫ x) xs
foldₗ : let _ = n in (B → A → B) → B → (A ^ n) → B
foldₗ(_▫_) = swap(elimIndepOp(const(_ → _)) id (swap(swap ∘ (_∘₂ (_▫_)))))

-------------------------------------------------------------------------------
-- Construction from other types

-- An empty tuple.
-- Example: empty = <>
empty : (T ^ 0)
empty = <>

-- A tuple with only a single element.
-- Example: singleton(x) = x
singleton : T → (T ^ 1)
singleton = id

fromSequence : (n : ℕ) → (𝕟(n) → T) → (T ^ n)
fromSequence(0)       f = <>
fromSequence(1)       f = f(𝟎)
fromSequence(𝐒(𝐒(n))) f = (f(𝟎) , fromSequence(𝐒(n)) (f ∘ 𝐒))

-- A tuple filled with a single element.
repeat : (n : ℕ) → T → (T ^ n)
repeat n = fromSequence n ∘ const

-------------------------------------------------------------------------------
-- Other

{-
intro : (n : ℕ) → ((i : ℕ) ⦃ ord : i < n ⦄ → (T ^ i) → T) → (T ^ n)
intro 0         _ = <>
intro 1         f = f(𝟎) <>
intro (𝐒(𝐒(n))) f =
  let rest = intro (𝐒(n)) (\i ⦃ ord ⦄ → f(i) ⦃ [≤]-successor ord ⦄)
  in  (f(𝐒(n)) ⦃ [<]-of-[𝐒] ⦄ rest , rest)
-}

mapReduceᵣ : let _ = n in (A → A → A) → B → (A → B) → (A ^ n) → B
mapReduceᵣ{𝟎}    (_▫_) def _   = const def
mapReduceᵣ{𝐒(n)} (_▫_) def map = map ∘ reduceᵣ{n} (_▫_)

-- Example: map₂(_▫_) (a₁,b₁,c₁,d₁) (a₂,b₂,c₂,d₂) = (a₁ ▫ a₂ , b₁ ▫ b₂ , c₁ ▫ c₂ , d₁ ▫ d₂)
map₂ : let _ = n in (A₁ → A₂ → B) → ((A₁ ^ n) → (A₂ ^ n) → (B ^ n))
map₂{0}       _ _        _        = <>
map₂{1}       f x        y        = f x y
map₂{𝐒(𝐒(n))} f (x , xs) (y , ys) = (f x y , map₂{𝐒(n)} f xs ys)

-- Transposes two tuples of the same length to one tuple of tuples containing the pairs.
transpose₂ : let _ = n in (A ^ n) → (B ^ n) → ((A ⨯ B) ^ n)
transpose₂ = map₂(_,_)

-- The first element of a tuple.
-- Example: head(a,b,c) = a
head : ⦃ pos : Positive(n) ⦄ → (T ^ n) → T
head{1}       x       = x
head{𝐒(𝐒(_))} (x , _) = x

-- The tuple without its first element.
-- Example: tail(a,b,c) = (b,c)
tail : ⦃ pos : Positive(n) ⦄ → (T ^ n) → (T ^ 𝐏(n))
tail{1}       _       = <>
tail{𝐒(𝐒(_))} (_ , x) = x

-- The element at the specified position of a tuple.
-- Example: index(2)(a,b,c,d) = c
index : 𝕟(n) → (T ^ n) → T
index{𝐒(_)} 𝟎      = head
index{𝐒(n)} (𝐒(i)) = index{n} i ∘ tail{𝐒(n)}

-- The tuple without the element at the specified position.
-- Example: without(2)(a,b,c,d) = (a,b,d)
without : ⦃ pos : Positive(n) ⦄ → 𝕟(n) → (T ^ n) → (T ^ 𝐏(n))
without {1}       𝟎      = const <>
without {𝐒(𝐒(n))} 𝟎      = tail{𝐒(𝐒(n))}
without {𝐒(𝐒(n))} (𝐒(i)) (x , l) = x ⊰ without {𝐒(n)} i l

mapAt : 𝕟(n) → (T → T) → (T ^ n) → (T ^ n)
mapAt {1}       𝟎        = Fn._$_
mapAt {𝐒(𝐒(n))} 𝟎      f = Tuple.map f id
mapAt {𝐒(𝐒(n))} (𝐒(i)) f = Tuple.map id (mapAt{𝐒(n)} i f)

-- Concatenates two tuples.
-- Example: (1,2,3,4) ++ (5,6) = (1,2,3,4,5,6)
_++_ : let _ = n₁ ; _ = n₂ in (T ^ n₁) → (T ^ n₂) → (T ^ (n₁ + n₂))
_++_ {0}        _        ys = ys
_++_ {1}        x        ys = x ⊰ ys
_++_ {𝐒(𝐒(n₁))} (x , xs) ys = x ⊰ (_++_ {𝐒(n₁)} xs ys)

-- Concatenates all tuples in the specified tuple of tuples.
-- Example: concat((1,2,3),(4,5,6)) = (1,2,3,4,5,6)
concat : let _ = n₁ ; _ = n₂ in ((T ^ n₁) ^ n₂) → (T ^ (n₁ ⋅ n₂))
concat {_} {0}        _          = <>
concat {_} {1}        xs         = xs
concat {n₁}{𝐒(𝐒(n₂))} (xs , xss) = _++_ {n₁}{n₁ ⋅ 𝐒(n₂)} xs (concat {n₁}{𝐒(n₂)} xss)

-- Transposes the specified tuple of tuples.
-- Example: transpose((1,(2,3)),(4,(5,6)),(7,(8,9))) = (((1,(4,7)),(2,(5,8)),(3,(6,9))))
transpose : let _ = n₁ ; _ = n₂ in ((T ^ n₁) ^ n₂) → ((T ^ n₂) ^ n₁)
transpose {n₁}       {0}        <>       = repeat n₁ <>
transpose {_}        {1}        x        = x
transpose {n₁}       {𝐒(𝐒(n₂))} (x , xs) = transpose₂{n₁} x (transpose{n₁}{𝐒(n₂)} xs)
