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
-- Note: `∀{l} → (tails l = accumulateIterate (length l) tail l)`.
tails : List(T) → List(List(T))
tails ∅       = singleton(∅)
tails (x ⊰ l) = (x ⊰ l) ⊰ tails l

-- Applies a binary operator to each element in the list left-associativitely, and starting with the initial element.
-- This means that the initial element will be the left-most and the most deeply nested element.
-- Example:
--   foldₗ(▫)(init)[]          = init
--   foldₗ(▫)(init)[a]         = init ▫ a
--   foldₗ(▫)(init)[a,b]       = (init ▫ a)▫b
--   foldₗ(▫)(init)[a,b,c,d,e] = ((((init ▫ a) ▫ b) ▫ c) ▫ d) ▫ e
foldₗ : (Result → T → Result) → Result → List(T) → Result
foldₗ _   result ∅          = result
foldₗ _▫_ result (elem ⊰ l) = foldₗ _▫_ (result ▫ elem) l

-- Applies a binary operator to each element in the list right-associativitely, and starting with the initial element.
-- This means that the initial element will be the right-most and the most deeply nested element.
-- Example:
--   foldᵣ(▫)(init)[]          = init
--   foldᵣ(▫)(init)[a]         = a ▫ init
--   foldᵣ(▫)(init)[a,b]       = a ▫ (b ▫ init)
--   foldᵣ(▫)(init)[a,b,c,d,e] = a ▫ (b ▫ (c ▫ (d ▫ (e ▫ init))))
foldᵣ : (T → Result → Result) → Result → List(T) → Result
foldᵣ _   init ∅          = init
foldᵣ _▫_ init (elem ⊰ l) = elem ▫ (foldᵣ _▫_ init l)

-- Applies a binary operator to each element in the list right-associativitely, and ending with the initial element.
-- This means that the initial element will be the left-most and the least deeply nested element.
-- Example:
--   foldInitᵣ(▫)(init)[]          = init
--   foldInitᵣ(▫)(init)[a]         = init ▫ a
--   foldInitᵣ(▫)(init)[a,b]       = init ▫ (a ▫ b)
--   foldInitᵣ(▫)(init)[a,b,c,d,e] = init ▫ (a ▫ (b ▫ (c ▫ (d ▫ e))))
-- Same as (reduceOrᵣ (_▫_) (a) (a⊰l)) except that
-- this allows matching out one element when
-- there is only a first element as the head
--  and an _arbitrary_ list as the tail.
-- Also, this differs from foldᵣ in the following way:
--   foldᵣ      (_▫_) (1) [2,3] = 2 ▫ (3 ▫ 1)
--   foldInitᵣ (_▫_) (1) [2,3] = 1 ▫ (2 ▫ 3)
-- Also: foldInitᵣ(▫)(init)(l++[last]) = foldᵣ(▫)(last)(init⊰l)
foldInitᵣ : (T → T → T) → T → List(T) → T
foldInitᵣ _   init ∅          = init
foldInitᵣ _▫_ init (elem ⊰ l) = init ▫ (foldInitᵣ _▫_ elem l)

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
reduceOrᵣ _▫_ init (elem ⊰ l) = foldInitᵣ _▫_ elem l

-- Accumulates the results of every step in `foldₗ` into a list.
-- Example:
--   accumulateFoldₗ(_▫_) result []        = [result]
--   accumulateFoldₗ(_▫_) result [a]       = [result▫a]
--   accumulateFoldₗ(_▫_) result [a,b]     = [result▫a , (result▫a)▫b]
--   accumulateFoldₗ(_▫_) result [a,b,c]   = [result▫a , (result▫a)▫b , ((result▫a)▫b)▫c]
--   accumulateFoldₗ(_▫_) result [a,b,c,d] = [result▫a , (result▫a)▫b , ((result▫a)▫b)▫c , (((result▫a)▫b)▫c)▫d]
accumulateFoldₗ : (Result → T → Result) → Result → List(T) → List(Result)
accumulateFoldₗ(_▫_) result ∅       = singleton(result)
accumulateFoldₗ(_▫_) result (x ⊰ l) = result ⊰ accumulateFoldₗ(_▫_) (result ▫ x) l

-- Accumulates the results of every step in `reduceₗ` into a list.
-- Example:
--   accumulateReduceₗ(_▫_) []        = []
--   accumulateReduceₗ(_▫_) [a]       = [a]
--   accumulateReduceₗ(_▫_) [a,b]     = [a , a▫b]
--   accumulateReduceₗ(_▫_) [a,b,c]   = [a , a▫b , (a▫b)▫c]
--   accumulateReduceₗ(_▫_) [a,b,c,d] = [a , a▫b , (a▫b)▫c , ((a▫b)▫c)▫d]
accumulateReduceₗ : (T → T → T) → List(T) → List(T)
accumulateReduceₗ(_▫_) ∅       = ∅
accumulateReduceₗ(_▫_) (x ⊰ l) = accumulateFoldₗ(_▫_) x l

-- Accumulates the results of every step in `_^_` into a list.
-- Example:
--   accumulateIterate₀ 0 f(x) = []
--   accumulateIterate₀ 1 f(x) = [x]
--   accumulateIterate₀ 2 f(x) = [x , f(x)]
--   accumulateIterate₀ 3 f(x) = [x , f(x) , f(f(x))]
--   accumulateIterate₀ 4 f(x) = [x , f(x) , f(f(x)) , f(f(f(x)))]
accumulateIterate₀ : ℕ → (T → T) → (T → List(T))
accumulateIterate₀ 𝟎      f(x) = ∅
accumulateIterate₀ (𝐒(n)) f(x) = x ⊰ accumulateIterate₀ n f (f(x))

-- Accumulates the results of every step in `_^_` into a list.
-- Example:
--   accumulateIterate 0 f(x) = [x]
--   accumulateIterate 1 f(x) = [x , f(x)]
--   accumulateIterate 2 f(x) = [x , f(x) , f(f(x))]
--   accumulateIterate 3 f(x) = [x , f(x) , f(f(x)) , f(f(f(x)))]
--   accumulateIterate 4 f(x) = [x , f(x) , f(f(x)) , f(f(f(x))) , f(f(f(f(x))))]
accumulateIterate : ℕ → (T → T) → (T → List(T))
accumulateIterate n = accumulateIterate₀(𝐒(n))

-- List concatenation.
-- Concatenates (joins/glues) two lists together.
-- Examples:
--   [] ++ [] = []
--   [a] ++ [b] = [a,b]
--   [a,b,c] ++ [d,e,f] = [a,b,c,d,e,f]
_++_ : List(T) → List(T) → List(T)
_++_ = swap(foldᵣ(_⊰_))

-- Concatenates multiple lists together.
-- Examples:
--   concat [[a,b,c] , [d,e] , [f] , [g,h]]
--   = [a,b,c] ++ [d,e] ++ [f] ++ [g,h] =
--   = [a,b,c,d,e,f,g,h]
concat : List(List(T)) → List(T)
concat = foldᵣ(_++_) ∅

-- Postpends an element to a list, inserting it to the end of the list.
-- Examples:
--   postpend a []      = [a]
--   postpend b [a]     = [a,b]
--   postpend c [a,b]   = [a,b,c]
--   postpend d [a,b,c] = [a,b,c,d]
postpend : T → List(T) → List(T)
postpend a ∅       = a ⊰ ∅
postpend a (x ⊰ l) = x ⊰ postpend a l

-- Inserts an element to a list, inserting it at the given position of the list.
-- If the given position is out of range, then the element is postpended to the list.
-- Examples:
--   insert 2 x []        = [x]
--   insert 2 x [a]       = [a,x]
--   insert 2 x [a,b]     = [a,b,x]
--   insert 2 x [a,b,c]   = [a,b,x,c]
--   insert 2 x [a,b,c,d] = [a,b,x,c,d]
insert : ℕ → T → List(T) → List(T)
insert 𝟎                = _⊰_
insert (𝐒(_)) a ∅       = singleton a
insert (𝐒(i)) a (x ⊰ l) = x ⊰ insert i a l

module LongOper where
  pattern empty = ∅
  pattern prepend elem list = elem ⊰ list

-- Applies a function on each element in the list
-- Examples:
--   map f[]      = []
--   map f[a]     = [f(a)]
--   map f[a,b]   = [f(a),f(b)]
--   map f[a,b,c] = [f(a),f(b),f(c)]
map : (A → B) → (List(A) → List(B))
map _ ∅ = ∅
map f (x ⊰ l) = f(x) ⊰ (map f l)

-- Filters the list while mapping it
mapFilter : (A → Option(B)) → (List(A) → List(B))
mapFilter _ ∅       = ∅
mapFilter f (x ⊰ l) = Option.partialMap id (_⊰_) (f(x)) (mapFilter f l)

-- Maps every element to a list in the given list and then concatenates the resulting list.
-- Note: Functionally equivalent to: `concat ∘₂ map`.
-- Example: `concatMap(x ↦ [x , x + 1 , x + 2]) [10,20,30,40] = [10,11,12 , 20,21,22 , 30,31,32 , 40,41,42]`
-- Alternative implementation:
--   concatMap f ∅ = ∅
--   concatMap f (x ⊰ l) = f(x) ++ concatMap f l
concatMap : (A → List(B)) → (List(A) → List(B))
concatMap f = foldᵣ((_++_) ∘ f) ∅

-- The nth element in the list
-- Examples:
-- • `index₀ 0 [a,b,c] = Some a`
-- • `index₀ 1 [a,b,c] = Some b`
-- • `index₀ 2 [a,b,c] = Some c`
-- • `index₀ 3 [a,b,c] = None`
-- • `index₀ 4 [a,b,c] = None`
index₀ : ℕ → List(T) → Option(T)
index₀ _      ∅       = Option.None
index₀ 𝟎      (x ⊰ _) = Option.Some(x)
index₀ (𝐒(n)) (_ ⊰ l) = index₀ n l

-- The sublist with the first n elements in the list.
-- Also called: "take" in the Haskell standard library.
-- Example:
-- • `initial 0 [1,2,3] = []`
-- • `initial 1 [1,2,3] = [1]`
-- • `initial 2 [1,2,3] = [1,2]`
-- • `initial 3 [1,2,3] = [1,2,3]`
-- • `initial 4 [1,2,3] = [1,2,3]`
-- • `initial 5 [1,2,3] = [1,2,3]`
initial : ℕ → List(T) → List(T)
initial _      ∅       = ∅
initial 𝟎      (_ ⊰ _) = ∅
initial (𝐒(n)) (x ⊰ l) = x ⊰ (initial n l)

-- The sublist without the first n elements in the list
-- Example:
-- • `skip 0 [1,2,3] = [1,2,3]`
-- • `skip 1 [1,2,3] = [2,3]`
-- • `skip 2 [1,2,3] = [3]`
-- • `skip 3 [1,2,3] = []`
-- • `skip 4 [1,2,3] = []`
-- • `skip 5 [1,2,3] = []`
skip : ℕ → List(T) → List(T)
skip _      ∅         = ∅
skip 𝟎      l@(_ ⊰ _) = l
skip (𝐒(n)) (x ⊰ l)   = skip n l

-- Extracts the first element from the list if there is one.
-- Example: `splitFirst [1,2,3] = Some(1 , [2,3])`
splitFirst : List(T) → Option(T ⨯ List(T))
splitFirst ∅       = Option.None
splitFirst (x ⊰ l) = Option.Some(x , l)

-- Extracts the last element from the list if there is one.
-- Example: `splitLast [1,2,3] = Some([1,2] , 3)`
splitLast : List(T) → Option(List(T) ⨯ T)
splitLast ∅           = Option.None
splitLast (x ⊰ ∅)     = Option.Some(∅ , x)
splitLast (x ⊰ y ⊰ l) = Option.map (Tuple.mapLeft (x ⊰_)) (splitLast (y ⊰ l))

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

-- Length of the list (number of elements in the list).
-- Examples:
-- • `length []      = 0`
-- • `length [a]     = 1`
-- • `length [a,b]   = 2`
-- • `length [b,a]   = 2`
-- • `length [a,b,c] = 3`
-- • `length [b,c,a] = 3`
-- • `length [c,a,b] = 3`
-- • `length [b,a,c] = 3`
-- • `length [a,c,b] = 3`
-- • `length [b,a,c] = 3`
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

-- Reverse the order of the elements in the list.
-- Example: `reverse [a,b,c,d] = [d,c,b,a]`.
reverse : List(T) → List(T)
reverse ∅ = ∅
reverse (x ⊰ l) = postpend x (reverse l)

import Function.Iteration as Function

-- The list with a list concatenated (repeated) n times.
-- Example: `[a,b,c] ++^ 4 = [a,b,c] ++ [a,b,c] ++ [a,b,c] ++ [a,b,c] = [a,b,c , a,b,c , a,b,c , a,b,c]`.
_++^_ : List(T) → ℕ → List(T)
_++^_ l n = Function.repeatᵣ n (_++_) l ∅

-- The list with an element repeated n times
-- Example: `repeat a 4 = [a,a,a,a]`.
repeat : T → ℕ → List(T)
repeat = (_++^_) ∘ singleton

-- Whether at least one element in the list satisfies the given boolean predicate function.
-- Note: `∀{pred}{l} → (satisfiesAny pred l = foldᵣ((_||_) ∘ pred) 𝐹 l)`. They are functionally equivalent but the difference is that this exits early when something false is found which is good for performance.
satisfiesAny : (T → Bool) → List(T) → Bool
satisfiesAny pred ∅       = 𝐹
satisfiesAny pred (x ⊰ l) with pred(x)
... | 𝑇 = 𝑇
... | 𝐹 = satisfiesAny(pred)(l)

-- Whether all elements in the list satisfies the given boolean predicate function.
-- Note: `∀{pred}{l} → (satisfiesAll pred l = foldᵣ((_&&_) ∘ pred) 𝑇 l)`. They are functionally equivalent but the difference is that this exits early when something false is found which is good for performance.
satisfiesAll : (T → Bool) → List(T) → Bool
satisfiesAll pred ∅       = 𝑇
satisfiesAll pred (x ⊰ l) with pred(x)
... | 𝑇 = satisfiesAll(pred)(l)
... | 𝐹 = 𝐹

satisfiesAll₂ : (T → T → Bool) → (T → List(T) → Bool) → (T → List(T) → Bool) → (List(T) → List(T) → Bool)
satisfiesAll₂(_▫_) l r ∅          ∅          = 𝑇
satisfiesAll₂(_▫_) l r (x ⊰ l₁)   ∅          = l x l₁
satisfiesAll₂(_▫_) l r ∅          (x ⊰ l₂)   = r x l₂
satisfiesAll₂(_▫_) l r (x₁ ⊰ l₁)  (x₂ ⊰ l₂) with (x₁ ▫ x₂)
... | 𝑇 = satisfiesAll₂(_▫_) l r l₁ l₂
... | 𝐹 = 𝐹

satisfiesAny₂ : (T → T → Bool) → (T → List(T) → Bool) → (T → List(T) → Bool) → (List(T) → List(T) → Bool)
satisfiesAny₂(_▫_) l r ∅          ∅          = 𝑇
satisfiesAny₂(_▫_) l r (x ⊰ l₁)   ∅          = l x l₁
satisfiesAny₂(_▫_) l r ∅          (x ⊰ l₂)   = r x l₂
satisfiesAny₂(_▫_) l r (x₁ ⊰ l₁)  (x₂ ⊰ l₂) with (x₁ ▫ x₂)
... | 𝑇 = 𝑇
... | 𝐹 = satisfiesAny₂(_▫_) l r l₁ l₂

{-satisfiesAll₂(_▫_) l r (x₁ ⊰ l₁)  (x₂ ⊰ l₂)  with (x₁ ▫ x₂)
... | 𝑇 = satisfiesAll₂(_▫_) l r l₁ l₂
... | 𝐹 = 𝐹-}

-- TODO
-- List-apply : ∀{L : List(Type{ℓ})} → (foldᵣ (_⨯_) (Out) (L)) → ∀{Out : Type{ℓ}} → (foldᵣ (_→ᶠ_) (Out) (L)) → Out
-- List-apply(∅)           (f) = f
-- List-apply(head ⊰ rest) (f) = List-apply(rest) (f(head))

-- fn-to-list : ∀{L : List(Type{ℓ})}{Out : Type{ℓ}} → (foldᵣ (_→ᶠ_) (Out) (L)) → (List(Type{ℓ}) → Out)
-- fn-to-list{∅} = 

-- Replacing the nth element in the list.
-- Example: `modifyAt 2 f [a,b,c,d] = [a,b,f(c),d]`.
modifyAt : ℕ → (T → T) → List(T) → List(T)
modifyAt _      f ∅       = ∅
modifyAt 𝟎      f (x ⊰ l) = f(x) ⊰ l
modifyAt (𝐒(n)) f (x ⊰ l) = x ⊰ modifyAt n f l

-- Example: `replaceAt 2 x [a,b,c,d] = [a,b,x,d]`.
replaceAt : ℕ → T → List(T) → List(T)
replaceAt n = modifyAt n ∘ const

-- The list without the nth element in the list
-- Example: `withoutIndex 2 [a,b,c,d] = [a,b,d]`.
withoutIndex : ℕ → List(T) → List(T)
withoutIndex _       ∅       = ∅
withoutIndex 𝟎       (_ ⊰ l) = l
withoutIndex (𝐒(n))  (x ⊰ l) = x ⊰ withoutIndex(n)(l)

-- Example: `swapIndex 1 3 [a,b,c,d,e,f] = [a,d,c,b,e,f]`.
swapIndex : ℕ → ℕ → List(T) → List(T)
swapIndex _      _      ∅      = ∅
swapIndex 𝟎      𝟎      (x ⊰ l) = (x ⊰ l)
swapIndex (𝐒(a)) 𝟎      (x ⊰ l) = Option.map(_⊰ replaceAt a x l) (index₀ a l) Option.or (x ⊰ l)
swapIndex 𝟎      (𝐒(b)) (x ⊰ l) = Option.map(_⊰ replaceAt b x l) (index₀ b l) Option.or (x ⊰ l)
swapIndex (𝐒(a)) (𝐒(b)) (x ⊰ l) = x ⊰ swapIndex a b l

-- The given list with only the elements that satisfy the given predicate (without the elements that do not satisfy the given predicate).
-- Example: `filter(_<? 10) [0,10,11,1,2,12,3,13,14,4,5] = [0,1,2,3,4,5]`.
filter : (T → Bool) → List(T) → List(T)
filter f(∅)     = ∅
filter f(x ⊰ l) = (if f(x) then (x ⊰_) else id) (filter f(l))

filterFirst : (T → Bool) → List(T) → List(T)
filterFirst f(∅)     = ∅
filterFirst f(x ⊰ l) with f(x)
... | 𝑇 = l
... | 𝐹 = x ⊰ filterFirst f(l)

-- Finds the first element that satisfies the given predicate in the given list.
find : (T → Bool) → List(T) → Option(T)
find f(∅)     = Option.None
find f(x ⊰ l) with f(x)
... | 𝑇 = Option.Some(x)
... | 𝐹 = find f(l)

-- Finds and extracts the first element satisfying the given predicate.
-- Example: `extractFirst(_> 2) [0,1,2,3,4,5] = Some(3 , [0,1,2,4,5])`.
extractFirstBy : (T → Bool) → List(T) → Option(T ⨯ List(T))
extractFirstBy f(∅)     = Option.None
extractFirstBy f(x ⊰ l) with f(x)
... | 𝑇 = Option.Some(x , l)
... | 𝐹 = Option.map(Tuple.mapRight(x ⊰_)) (extractFirstBy f(l))

-- The number of elements satisfying the given predicate in the given list.
count : (T → Bool) → List(T) → ℕ
count f(∅)     = 𝟎
count f(x ⊰ l) = (if f(x) then 𝐒 else id) (count f(l))

-- Whether the given list is the empty list.
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

-- Example:
--   interleave [[0,1,2],[10,11,12,13,14],[100,101]] = [0,10,100 , 1,11,101 , 2,12 , 13 , 14]
-- Termination:
--   Terminates because the argument in the recursion `map tail ls` shrinks every list until they all become empty, and when all lists are empty, the function branches to the other trivially terminating case.
{-# TERMINATING #-}
interleave : List(List(T)) → List(T)
interleave ls with satisfiesAll isEmpty ls
... | 𝑇 = ∅
... | 𝐹 = foldᵣ (Option.partialMap id (_⊰_) ∘ first) (interleave(map tail ls)) ls

-- Note: This is similiar to a function called `zipWith` in the Haskell standard library. Specifically, `map₂(_▫_) (const ∅) (const ∅) ⊜ zipWith(_▫_)`.
-- TODO: Generalize like https://stackoverflow.com/questions/39991581/how-can-i-implement-generalized-zipn-and-unzipn-in-haskell
map₂ : (A₁ → A₂ → B) → (List(A₁) → List(B)) → (List(A₂) → List(B)) → (List(A₁) → List(A₂) → List(B))
map₂ f g₁ g₂ ∅          ∅          = ∅
map₂ f g₁ g₂ ∅          l₂@(_ ⊰ _) = g₂ l₂
map₂ f g₁ g₂ l₁@(_ ⊰ _) ∅          = g₁ l₁
map₂ f g₁ g₂ (x₁ ⊰ l₁)  (x₂ ⊰ l₂)  = f x₁ x₂ ⊰ map₂ f g₁ g₂ l₁ l₂

-- Rotates to the left.
-- Example:
--   (rotateₗ ^ 3) [a,b,c,d,e]
--   = (rotateₗ ^ 2) [b,c,d,e,a]
--   = (rotateₗ ^ 1) [c,d,e,a,b]
--   = (rotateₗ ^ 0) [d,e,a,b,c]
--   = [d,e,a,b,c]
rotateₗ : List(T) → List(T)
rotateₗ ∅       = ∅
rotateₗ (x ⊰ l) = postpend x l

-- Rotates to the right.
-- Example:
--   (rotateᵣ ^ 3) [a,b,c,d,e]
--   = (rotateᵣ ^ 2) [e,a,b,c,d]
--   = (rotateᵣ ^ 1) [d,e,a,b,c]
--   = (rotateᵣ ^ 0) [c,d,e,a,b]
--   = [b,c,d,e,a]
rotateᵣ : List(T) → List(T)
rotateᵣ l = Option.partialMap ∅ (Tuple.uncurry(swap(_⊰_))) (splitLast l)

-- Examples:
--   every n [] = []
--   every 0  [0,1,2,3,4,5,6,7,8] = []
--   every 1  [0,1,2,3,4,5,6,7,8] = [0,1,2,3,4,5,6,7,8]
--   every 2  [0,1,2,3,4,5,6,7,8] = [0,2,4,6,8]
--   every 3  [0,1,2,3,4,5,6,7,8] = [0,3,6]
--   every 4  [0,1,2,3,4,5,6,7,8] = [0,4,8]
--   every 5  [0,1,2,3,4,5,6,7,8] = [0,5]
--   every 6  [0,1,2,3,4,5,6,7,8] = [0,6]
--   every 7  [0,1,2,3,4,5,6,7,8] = [0,7]
--   every 8  [0,1,2,3,4,5,6,7,8] = [0,8]
--   every 9  [0,1,2,3,4,5,6,7,8] = [0]
--   every 10 [0,1,2,3,4,5,6,7,8] = [0]
-- Alternative implementations:
-- • every n l = map head (accumulateIterate₀ (length(n) ⌈/₀⌉ n) (skip n) l)
--   every 0         _       = ∅
--   every 1         l       = l
--   every (𝐒(𝐒(n))) ∅       = ∅
-- • every (𝐒(𝐒(n))) (x ⊰ l) = x ⊰ every (𝐒(𝐒(n))) (skip (𝐒(n)) l)
every : ℕ → List(T) → List(T)
every 𝟎      = const ∅
every (𝐒(n)) = impl 𝟎 where
  -- TODO: Is it possible to prove stuff about `every` when `impl` is hidden in a where clause? `impl` essentially contains a counter, so an alternative implementation would be having `every` have two arguments.
  impl : ℕ → List(T) → List(T)
  impl _     ∅       = ∅
  impl 𝟎     (x ⊰ l) = x ⊰ impl n l
  impl (𝐒 k) (x ⊰ l) = impl k l

-- Examples:
--   separate 0  [0,1,2,3,4,5,6,7,8] = []
--   separate 1  [0,1,2,3,4,5,6,7,8] = [[0,1,2,3,4,5,6,7,8]]
--   separate 2  [0,1,2,3,4,5,6,7,8] = [[0,2,4,6,8],[1,3,5,7]]
--   separate 3  [0,1,2,3,4,5,6,7,8] = [[0,3,6],[1,4,7],[2,5,8]]
--   separate 4  [0,1,2,3,4,5,6,7,8] = [[0,4,8],[1,5],[2,6],[3,7]]
--   separate 5  [0,1,2,3,4,5,6,7,8] = [[0,5],[1,6],[2,7],[3,8],[4]]
--   separate 6  [0,1,2,3,4,5,6,7,8] = [[0,6],[1,7],[2,8],[3],[4],[5]]
--   separate 7  [0,1,2,3,4,5,6,7,8] = [[0,7],[1,8],[2],[3],[4],[5],[6]]
--   separate 8  [0,1,2,3,4,5,6,7,8] = [[0,8],[1],[2],[3],[4],[5],[6],[7]]
--   separate 9  [0,1,2,3,4,5,6,7,8] = [[0],[1],[2],[3],[4],[5],[6],[7],[8]]
--   separate 10 [0,1,2,3,4,5,6,7,8] = [[0],[1],[2],[3],[4],[5],[6],[7],[8],[]]
--   separate 11 [0,1,2,3,4,5,6,7,8] = [[0],[1],[2],[3],[4],[5],[6],[7],[8],[],[]]
separate : ℕ → List(T) → List(List(T))
separate n l = map (every n) (accumulateIterate₀ n tail l)

insertIn : T → (l : List(T)) → 𝕟₌(length l) → List(T)
insertIn a l       𝟎      = a ⊰ l
insertIn a ∅       (𝐒(_)) = singleton a
insertIn a (x ⊰ l) (𝐒(i)) = x ⊰ insertIn a l i

foldUntilᵣ : (A → Option(B → B)) → (List(A) → B) → List(A) → B
foldUntilᵣ f i ∅ = i(∅)
foldUntilᵣ f i (x ⊰ l) with f(x)
... | Option.None   = i(x ⊰ l)
... | Option.Some s = s(foldUntilᵣ f i l)

-- Also called: groupBy (Haskell) (Though there is a difference in behaviour. The first element in every group is used to compare to all the successive in the group).
-- Alternative implementation (accepted by the termination checker):
--   adjacencyPartition f(∅)     = ∅
--   adjacencyPartition f(x ⊰ l) with adjacencyPartition f(l)
--   ... | ∅            = singleton(singleton x)
--   ... | ∅ ⊰ Ll       = (singleton x) ⊰ Ll
--   ... | (y ⊰ L) ⊰ Ll = if (f x y) then ((x ⊰ y ⊰ L) ⊰ Ll) else ((singleton x) ⊰ (y ⊰ L) ⊰ Ll)
-- Termination: `rest` is a strict sublist of `x ⊰ l` because foldUntilᵣ do not grow the right tuple value and it uses `l`.
-- Note: concat ∘ adjacencyPartition(_▫_) ≡ id
-- Example: adjacencyPartitionCount(_≡?_) [0,1,2,2,2,3,3,4,4,5,5,5,5,6] = [[0],[1],[2,2,2],[3,3],[4,4],[5,5,5,5],[6]]
{-# TERMINATING #-}
adjacencyPartition : (T → T → Bool) → List(T) → List(List(T))
adjacencyPartition f ∅      = ∅
adjacencyPartition f(x ⊰ l) =
  let (g , rest) = foldUntilᵣ(y ↦ (if(f x y) then Option.Some(Tuple.mapLeft (y ⊰_)) else Option.None)) (∅ ,_) l
  in (x ⊰ g) ⊰ adjacencyPartition f(rest)

-- Note: concatMap(Tuple.uncurry repeat) ∘ adjacencyPartitionCount(_▫_) ≡ id
-- Example: adjacencyPartitionCount(_≡?_) [0,1,2,2,2,3,3,4,4,5,5,5,5,6] = [(0,1) , (1,1) , (2,3) , (3,2) , (4,2) , (5,4) , (6,1)]
{-# TERMINATING #-}
adjacencyPartitionCount : (T → T → Bool) → List(T) → List(T ⨯ ℕ)
adjacencyPartitionCount f ∅      = ∅
adjacencyPartitionCount f(x ⊰ l) =
  let (n , rest) = foldUntilᵣ(y ↦ (if(f x y) then Option.Some(Tuple.mapLeft 𝐒) else Option.None)) (𝟏 ,_) l
  in (x , n) ⊰ adjacencyPartitionCount f(rest)
