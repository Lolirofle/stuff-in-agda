module Data.List.Functions where

import      Lvl
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data.List
open import Data.Option as Option using (Option)
import      Data.Option.Functions as Option
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Numeral.Finite
open import Numeral.Natural
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T A A₁ A₂ B B₁ B₂ Result : Type{ℓ}

infixl 1000 _++_

open import Data.List.Functions.Positional public

-- The list of the successive application of `tail` on a list.
-- For a list `l`, the range of `n ↦ (tail ^ n)(l)` as a list.
-- Example:
--   tails []      = [[]]
--   tails [a]     = [[a] , []]
--   tails [a,b]   = [[a,b] , [b] , []]
--   tails [a,b,c] = [[a,b,c] , [b,c] , [c] , []]
tails : List(T) → List(List(T))
tails ∅       = singleton(∅)
tails (x ⊰ l) = (x ⊰ l) ⊰ tails l

-- Applies a binary operator to each element in the list starting with the initial element.
-- Example:
--   foldₗ(▫)(init)[]          = init
--   foldₗ(▫)(init)[a]         = init▫a
--   foldₗ(▫)(init)[a,b]       = (init▫a)▫b
--   foldₗ(▫)(init)[a,b,c,d,e] = ((((init▫a)▫b)▫c)▫d)▫e
foldₗ : (Result → T → Result) → Result → List(T) → Result
foldₗ _   result ∅          = result
foldₗ _▫_ result (elem ⊰ l) = foldₗ _▫_ (result ▫ elem) l

-- Applies a binary operator to each element in the list starting with the initial element.
-- Example:
--   foldᵣ(▫)(init)[]          = init
--   foldᵣ(▫)(init)[a]         = a▫init
--   foldᵣ(▫)(init)[a,b]       = a▫(b▫init)
--   foldᵣ(▫)(init)[a,b,c,d,e] = a▫(b▫(c▫(d▫(e▫init))))
foldᵣ : (T → Result → Result) → Result → List(T) → Result
foldᵣ _   init ∅          = init
foldᵣ _▫_ init (elem ⊰ l) = elem ▫ (foldᵣ _▫_ init l)

-- Applies a binary operator to each element in the list starting with the initial element.
-- Example:
--   foldᵣ-init(▫)(init)[]          = init
--   foldᵣ-init(▫)(init)[a]         = init▫a
--   foldᵣ-init(▫)(init)[a,b]       = init▫(a▫b)
--   foldᵣ-init(▫)(init)[a,b,c,d,e] = init▫(a▫(b▫(c▫(d▫e))))
-- Same as (reduceOrᵣ (_▫_) (a) (a⊰l)) except that
-- this allows matching out one element when
-- there is only a first element as the head
--  and an _arbitrary_ list as the tail.
-- Also, this dIffers from foldᵣ in such a way that:
--   foldᵣ (_▫_) (1) [2,3] = 2 ▫ (3 ▫ 1)
--   foldᵣ-init (_▫_) (1) [2,3] = 1 ▫ (2 ▫ 3)
-- Also: foldᵣ-init(▫)(init)(l++[last]) = foldᵣ(▫)(last)(init⊰l)
foldᵣ-init : (T → T → T) → T → List(T) → T
foldᵣ-init _   init ∅          = init
foldᵣ-init _▫_ init (elem ⊰ l) = init ▫ (foldᵣ-init _▫_ elem l)

-- If the list is empty, use the result, else like foldₗ
-- Example:
--   reduceOrₗ(▫)(result)[]          = result
--   reduceOrₗ(▫)(result)[a]         = a
--   reduceOrₗ(▫)(result)[a,b]       = a▫b
--   reduceOrₗ(▫)(result)[a,b,c]     = (a▫b)▫c
--   reduceOrₗ(▫)(result)[a,b,c,d,e] = (((a▫b)▫c)▫d)▫e
reduceOrₗ : (T → T → T) → T → List(T) → T
reduceOrₗ _   result ∅          = result
reduceOrₗ _▫_ result (elem ⊰ l) = foldₗ _▫_ elem l

-- If the list is empty, use the result, else like foldᵣ
-- Example:
--   reduceOrᵣ(▫)(result)[]          = result
--   reduceOrᵣ(▫)(result)[a]         = a
--   reduceOrᵣ(▫)(result)[a,b]       = a▫b
--   reduceOrᵣ(▫)(result)[a,b,c]     = a▫(b▫c)
--   reduceOrᵣ(▫)(result)[a,b,c,d,e] = a▫(b▫(c▫(d▫e)))
reduceOrᵣ : (T → T → T) → T → List(T) → T
reduceOrᵣ _   init ∅          = init
reduceOrᵣ _▫_ init (elem ⊰ l) = foldᵣ-init _▫_ elem l

-- Accumulates the results of every step in `foldₗ` into a list.
-- Example:
--   accumulate-foldₗ(_▫_) result []        = [result]
--   accumulate-foldₗ(_▫_) result [a]       = [result▫a]
--   accumulate-foldₗ(_▫_) result [a,b]     = [result▫a , (result▫a)▫b]
--   accumulate-foldₗ(_▫_) result [a,b,c]   = [result▫a , (result▫a)▫b , ((result▫a)▫b)▫c]
--   accumulate-foldₗ(_▫_) result [a,b,c,d] = [result▫a , (result▫a)▫b , ((result▫a)▫b)▫c , (((result▫a)▫b)▫c)▫d]
accumulate-foldₗ : (Result → T → Result) → Result → List(T) → List(Result)
accumulate-foldₗ(_▫_) result ∅       = singleton(result)
accumulate-foldₗ(_▫_) result (x ⊰ l) = result ⊰ accumulate-foldₗ(_▫_) (result ▫ x) l

-- Accumulates the results of every step in `reduceₗ` into a list.
-- Example:
--   accumulate-reduceₗ(_▫_) []        = []
--   accumulate-reduceₗ(_▫_) [a]       = [a]
--   accumulate-reduceₗ(_▫_) [a,b]     = [a , a▫b]
--   accumulate-reduceₗ(_▫_) [a,b,c]   = [a , a▫b , (a▫b)▫c]
--   accumulate-reduceₗ(_▫_) [a,b,c,d] = [a , a▫b , (a▫b)▫c , ((a▫b)▫c)▫d]
accumulate-reduceₗ : (T → T → T) → List(T) → List(T)
accumulate-reduceₗ(_▫_) ∅       = ∅
accumulate-reduceₗ(_▫_) (x ⊰ l) = accumulate-foldₗ(_▫_) x l

-- List concatenation.
-- Concatenates (joins/glues) two lists together.
-- Examples:
--   [] ++ [] = []
--   [a] ++ [b] = [a,b]
--   [a,b,c] ++ [d,e,f] = [a,b,c,d,e,f]
_++_ : List(T) → List(T) → List(T)
_++_ = swap(foldᵣ (_⊰_))

-- Concatenates multiple lists together.
-- Examples:
--   concat [[a,b,c] , [d,e] , [f] , [g,h]]
--   = [a,b,c] ++ [d,e] ++ [f] ++ [g,h] =
--   = [a,b,c,d,e,f,g,h]
concat : List(List(T)) → List(T)
concat = foldᵣ(_++_) ∅

-- Postpends an element on a list, inserting it to the end of the list.
-- Examples:
--   postpend a []      = [a]
--   postpend b [a]     = [a,b]
--   postpend c [a,b]   = [a,b,c]
--   postpend d [a,b,c] = [a,b,c,d]
postpend : T → List(T) → List(T)
postpend a ∅       = a ⊰ ∅
postpend a (x ⊰ l) = x ⊰ postpend a l

module LongOper where
  pattern empty = ∅
  pattern prepend elem list = elem ⊰ list

-- Applies a function on each element in the list
-- Examples
--   map f[]      = []
--   map f[a]     = [f(a)]
--   map f[a,b]   = [f(a),f(b)]
--   map f[a,b,c] = [f(a),f(b),f(c)]
map : (A → B) → (List(A) → List(B))
map _ ∅ = ∅
map f (x ⊰ l) = f(x) ⊰ (map f l)

-- Filters the list while mapping it
mapFilter : (A → Option(B)) → (List(A) → List(B))
mapFilter _ ∅ = ∅
mapFilter f (x ⊰ l) with f(x)
... | Option.Some(y) = y ⊰ (mapFilter f l)
... | Option.None    = mapFilter f l

concatMap : (A → List(B)) → (List(A) → List(B))
concatMap f ∅ = ∅
concatMap f (x ⊰ l) = f(x) ++ concatMap f l

-- The nth element in the list
index₀ : ℕ → List(T) → Option(T)
index₀ _      ∅       = Option.None
index₀ 𝟎      (x ⊰ _) = Option.Some(x)
index₀ (𝐒(n)) (_ ⊰ l) = index₀ n l

-- The sublist with the first n elements in the list
initial : ℕ → List(T) → List(T)
initial _      ∅       = ∅
initial 𝟎      (_ ⊰ _) = ∅
initial (𝐒(n)) (x ⊰ l) = x ⊰ (initial n l)

-- The sublist without the first n elements in the list
skip : ℕ → List(T) → List(T)
skip _      ∅         = ∅
skip 𝟎      l@(_ ⊰ _) = l
skip (𝐒(n)) (x ⊰ l)   = skip n l

-- Split a list into two sublist parts at the specified index.
-- The first list's length is the specified index.
-- The second list starts at the specified index.
-- Example:
--   splitAt 0 [a,b,c,d] = ([] , [a,b,c,d])
--   splitAt 1 [a,b,c,d] = ([a] , [b,c,d])
--   splitAt 2 [a,b,c,d] = ([a,b] , [c,d])
--   splitAt 3 [a,b,c,d] = ([a,b,c] , [d])
--   splitAt 4 [a,b,c,d] = ([a,b,c,d] , [])
--   splitAt 5 [a,b,c,d] = ([a,b,c,d] , [])
splitAt : ℕ → List(T) → (List(T) ⨯ List(T))
splitAt 𝟎     l       = (∅ , l)
splitAt (𝐒 n) ∅       = (∅ , ∅)
splitAt (𝐒 n) (x ⊰ l) = Tuple.mapLeft (x ⊰_) (splitAt n l)

-- All ordered sublist partitions of the specified list with only two parts.
-- 
splits₂ : List(T) → List(List(T) ⨯ List(T))
splits₂ l = (∅ , l) ⊰ f ∅ l where
  f : List(T) → List(T) → List(List(T) ⨯ List(T))
  f _ ∅       = ∅
  f a (x ⊰ b) = (postpend x a , b) ⊰ f (postpend x a) b

-- Length of the list (number of elements in the list)
length : List(T) → ℕ
length = foldᵣ (const 𝐒) 0

-- The nth element in the list as a total function.
index : (l : List(T)) → 𝕟(length(l)) → T
index ∅       ()
index (x ⊰ l) 𝟎     = x
index (x ⊰ l) (𝐒 n) = index l n

-- The sublist with the last n elements in the list
-- last : ℕ → List(T) → List(T)
-- last n l = skip(length(l) −₀ ) l

-- TODO: Generalize
mapWindow2ₗ : (T → T → T) → List(T) → List(T)
mapWindow2ₗ f (x₁ ⊰ x₂ ⊰ l) = (f x₁ x₂) ⊰ (mapWindow2ₗ f (x₂ ⊰ l))
{-# CATCHALL #-}
mapWindow2ₗ _ _ = ∅

_orₗ_ : List(T) → List(T) → List(T)
_orₗ_ ∅ default      = default
_orₗ_ (l @(_ ⊰ _)) _ = l

-- Reverse the order of the elements in the list
reverse : List(T) → List(T)
reverse ∅ = ∅
reverse (x ⊰ l) = postpend x (reverse l)

import Function.Iteration as Function

-- The list with a list concatenated (repeated) n times
_++^_ : List(T) → ℕ → List(T)
_++^_ l n = Function.repeatᵣ n (_++_) l ∅

-- The list with an element repeated n times
repeat : T → ℕ → List(T)
repeat = (_++^_) ∘ singleton

satisfiesAny : (T → Bool) → List(T) → Bool
satisfiesAny pred ∅       = 𝐹
satisfiesAny pred (x ⊰ l) = pred(x) || satisfiesAny(pred)(l)

satisfiesAll : (T → Bool) → List(T) → Bool
satisfiesAll pred ∅       = 𝑇
satisfiesAll pred (x ⊰ l) = pred(x) && satisfiesAll(pred)(l)

-- TODO
-- List-apply : ∀{L : List(Type{ℓ})} → (foldᵣ (_⨯_) (Out) (L)) → ∀{Out : Type{ℓ}} → (foldᵣ (_→ᶠ_) (Out) (L)) → Out
-- List-apply(∅)           (f) = f
-- List-apply(head ⊰ rest) (f) = List-apply(rest) (f(head))

-- fn-to-list : ∀{L : List(Type{ℓ})}{Out : Type{ℓ}} → (foldᵣ (_→ᶠ_) (Out) (L)) → (List(Type{ℓ}) → Out)
-- fn-to-list{∅} = 

-- Replacing the nth element in the list
modifyAt : ℕ → (T → T) → List(T) → List(T)
modifyAt _      f ∅       = ∅
modifyAt 𝟎      f (x ⊰ l) = f(x) ⊰ l
modifyAt (𝐒(n)) f (x ⊰ l) = x ⊰ modifyAt n f l

replaceAt : ℕ → T → List(T) → List(T)
replaceAt n = modifyAt n ∘ const

-- The list without the nth element in the list
withoutIndex : ℕ → List(T) → List(T)
withoutIndex _       ∅       = ∅
withoutIndex 𝟎       (_ ⊰ l) = l
withoutIndex (𝐒(n))  (x ⊰ l) = x ⊰ withoutIndex(n)(l)

swapIndex : ℕ → ℕ → List(T) → List(T)
swapIndex _      _      ∅      = ∅
swapIndex 𝟎      𝟎      (x ⊰ l) = (x ⊰ l)
swapIndex (𝐒(a)) 𝟎      (x ⊰ l) = Option.map(_⊰ replaceAt a x l) (index₀ a l) Option.or (x ⊰ l)
swapIndex 𝟎      (𝐒(b)) (x ⊰ l) = Option.map(_⊰ replaceAt b x l) (index₀ b l) Option.or (x ⊰ l)
swapIndex (𝐒(a)) (𝐒(b)) (x ⊰ l) = x ⊰ swapIndex a b l

filter : (T → Bool) → List(T) → List(T)
filter f(∅)     = ∅
filter f(x ⊰ l) = if f(x) then (x ⊰ (filter f(l))) else (filter f(l))

find : (T → Bool) → List(T) → Option(T)
find f(∅)     = Option.None
find f(x ⊰ l) = if f(x) then Option.Some(x) else (find f(l))

count : (T → Bool) → List(T) → ℕ
count f(∅)     = 𝟎
count f(x ⊰ l) = (if f(x) then 𝐒 else id) (count f(l))

isEmpty : List(T) → Bool
isEmpty(∅)     = 𝑇
isEmpty(_ ⊰ _) = 𝐹

-- Separates a list into 2 lists of almost equal length putting every other element into different lists.
-- Example:
--   separate₂ []          = ([]      , [])
--   separate₂ [a]         = ([a]     , [])
--   separate₂ [a,b]       = ([a]     , [b])
--   separate₂ [a,b,c]     = ([a,c]   , [b])
--   separate₂ [a,b,c,d]   = ([a,c]   , [b,d])
--   separate₂ [a,b,c,d,e] = ([a,c,e] , [b,d])
separate₂ : List(T) → (List(T) ⨯ List(T))
separate₂ ∅           = (∅ , ∅)
separate₂ (x ⊰ ∅)     = (singleton x , ∅)
separate₂ (x ⊰ y ⊰ l) = Tuple.map (x ⊰_) (y ⊰_) (separate₂ l)

{-
module _ where
  open import Data.Tuple.Raise

  separate : (n : ℕ) → List(T) → (List(T) ^ n)
  separate = {!!}
-}

-- Note: This is similiar to a function called `zipWith` in the Haskell standard library.
-- TODO: Generalize like https://stackoverflow.com/questions/39991581/how-can-i-implement-generalized-zipn-and-unzipn-in-haskell
map₂ : (A₁ → A₂ → B) → (List(A₁) → List(B)) → (List(A₂) → List(B)) → (List(A₁) → List(A₂) → List(B))
map₂ f g₁ g₂ ∅          ∅          = ∅
map₂ f g₁ g₂ ∅          l₂@(_ ⊰ _) = g₂ l₂
map₂ f g₁ g₂ l₁@(_ ⊰ _) ∅          = g₁ l₁
map₂ f g₁ g₂ (x₁ ⊰ l₁)  (x₂ ⊰ l₂)  = f x₁ x₂ ⊰ map₂ f g₁ g₂ l₁ l₂

-- module _ where
--   open import Data.Tuple.Raise as Tuple using (_^_)
--   open import Function.Multi as Multi using (_⇉_)

  --map₊ : ∀{n}{As : Type{ℓ} ^ n}{B} → (As ⇉ B) → (Tuple.map List(As) ⇉ List(B))
  -- map₊ {n = 𝟎}                 = const ∅
  -- map₊ {n = 𝐒(𝟎)}              = map
  -- map₊ {n = 𝐒(𝐒(n))} _ ∅       = Multi.const ∅
  -- map₊ {n = 𝐒(𝐒(n))} f (x ⊰ l) = {!!}
