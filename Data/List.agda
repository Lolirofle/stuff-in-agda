module Data.List where

open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data.Option as Option using (Option)
open import Functional
open import Numeral.Natural
open import Type

infixl 1000 _⊱_ _++_
infixr 1000 _⊰_
infixl 1      [_
infixl 100000 _]

-- A list is a container/collection with elements in order and allowing multiples
data List {ℓ} (T : Type{ℓ}) : Type{ℓ} where
  ∅   : List(T) -- The empty list
  _⊰_ : T → List(T) → List(T) -- Cons

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  ∅  #-}
{-# BUILTIN CONS _⊰_ #-}

_⊱_ : ∀{ℓ}{T : Type{ℓ}} → List(T) → T → List(T)
_⊱_ = swap _⊰_

-- List concatenation
_++_ : ∀{ℓ}{T : Type{ℓ}} → List(T) → List(T) → List(T)
_++_ ∅ b = b
_++_ (elem ⊰ rest) b = elem ⊰ (rest ++ b)

module _ {ℓ₁ ℓ₂} where
  import      Lvl
  open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}

  List-induction : ∀{T : Type{ℓ₂}}{P : List(T) → Stmt} → P(∅) → (∀(x : T)(l : List(T)) → P(l) → P(x ⊰ l)) → (∀{l : List(T)} → P(l))
  List-induction base next {∅} = base
  List-induction base next {x ⊰ l} = next(x)(l)(List-induction base next {l})

module LongOper where
  pattern empty = ∅
  pattern prepend elem list = elem ⊰ list
  postpend = _⊱_
  concat   = _++_

-- The list with a single element
singleton : ∀{ℓ}{T : Type{ℓ}} → T → List(T)
singleton elem = elem ⊰ ∅

-- The list without its first element
tail : ∀{ℓ}{T : Type{ℓ}} → List(T) → List(T)
tail ∅ = ∅
tail (_ ⊰ l) = l

-- Applies a function to each element in the list
map : ∀{ℓ₁ ℓ₂}{T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → (T₁ → T₂) → List(T₁) → List(T₂)
map _ ∅ = ∅
map f (elem ⊰ l) = (f elem) ⊰ (map f l)

-- Applies a binary operator to each element in the list starting with the initial element.
-- Example:
--   foldₗ(▫)(init)[]          = init
--   foldₗ(▫)(init)[a]         = init▫a
--   foldₗ(▫)(init)[a,b]       = (init▫a)▫b
--   foldₗ(▫)(init)[a,b,c,d,e] = ((((init▫a)▫b)▫c)▫d)▫e
foldₗ : ∀{ℓ₁ ℓ₂}{T : Type{ℓ₁}}{Result : Type{ℓ₂}} → (Result → T → Result) → Result → List(T) → Result
foldₗ _   result ∅ = result
foldₗ _▫_ result (elem ⊰ l) = foldₗ _▫_ (result ▫ elem) l

-- Applies a binary operator to each element in the list starting with the initial element.
-- Example:
--   foldᵣ(▫)(init)[]          = init
--   foldᵣ(▫)(init)[a]         = a▫init
--   foldᵣ(▫)(init)[a,b]       = a▫(b▫init)
--   foldᵣ(▫)(init)[a,b,c,d,e] = a▫(b▫(c▫(d▫(e▫init))))
foldᵣ : ∀{ℓ₁ ℓ₂}{T : Type{ℓ₁}}{Result : Type{ℓ₂}} → (T → Result → Result) → Result → List(T) → Result
foldᵣ _   init ∅ = init
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
foldᵣ-init : ∀{ℓ}{T : Type{ℓ}} → (T → T → T) → T → List(T) → T
foldᵣ-init _   init ∅ = init
foldᵣ-init _▫_ init (elem ⊰ l) = init ▫ (foldᵣ-init _▫_ elem l)

-- If the list is empty, use the result, else like foldₗ
-- Example:
--   reduceOrₗ(▫)(result)[]          = result
--   reduceOrₗ(▫)(result)[a]         = a
--   reduceOrₗ(▫)(result)[a,b]       = a▫b
--   reduceOrₗ(▫)(result)[a,b,c]     = (a▫b)▫c
--   reduceOrₗ(▫)(result)[a,b,c,d,e] = (((a▫b)▫c)▫d)▫e
reduceOrₗ : ∀{ℓ}{T : Type{ℓ}} → (T → T → T) → T → List(T) → T
reduceOrₗ _   result ∅ = result
reduceOrₗ _▫_ result (elem ⊰ ∅) = elem
reduceOrₗ _▫_ result (elem₁ ⊰ (elem₂ ⊰ l)) = reduceOrₗ _▫_ (result ▫ elem₁) (elem₂ ⊰ l)

-- If the list is empty, use the result, else like foldᵣ
-- Example:
--   reduceOrᵣ(▫)(result)[]          = result
--   reduceOrᵣ(▫)(result)[a]         = a
--   reduceOrᵣ(▫)(result)[a,b]       = a▫b
--   reduceOrᵣ(▫)(result)[a,b,c]     = a▫(b▫c)
--   reduceOrᵣ(▫)(result)[a,b,c,d,e] = a▫(b▫(c▫(d▫e)))
reduceOrᵣ : ∀{ℓ}{T : Type{ℓ}} → (T → T → T) → T → List(T) → T
reduceOrᵣ _   init ∅ = init
reduceOrᵣ _▫_ init (elem ⊰ ∅) = elem
reduceOrᵣ _▫_ init (elem₁ ⊰ (elem₂ ⊰ l)) = elem₁ ▫ (reduceOrᵣ _▫_ init (elem₂ ⊰ l))

-- The nth element in the list
index : ∀{ℓ}{T : Type{ℓ}} → ℕ → List(T) → Option(T)
index _      ∅       = Option.None
index 𝟎      (x ⊰ _) = Option.Some(x)
index (𝐒(n)) (_ ⊰ l) = index n l

-- The sublist with the first n elements in the list
first : ∀{ℓ}{T : Type{ℓ}} → ℕ → List(T) → List(T)
first _      ∅       = ∅
first 𝟎      (x ⊰ _) = x ⊰ ∅
first (𝐒(n)) (x ⊰ l) = x ⊰ (first n l)

-- Length of the list (number of elements in the list)
length : ∀{ℓ}{T : Type{ℓ}} → List(T) → ℕ
length ∅ = 𝟎
length (_ ⊰ l) = 𝐒(length l)
-- foldᵣ (_ count ↦ 𝐒(count)) 0 l

-- TODO: Generalize
mapWindow2ₗ : ∀{ℓ}{T : Type{ℓ}} → (T → T → T) → List(T) → List(T)
mapWindow2ₗ f (x₁ ⊰ x₂ ⊰ l) = (f x₁ x₂) ⊰ (mapWindow2ₗ f (x₂ ⊰ l))
mapWindow2ₗ _ _ = ∅

-- The first element of the list (head)
firstElem : ∀{ℓ}{T : Type{ℓ}} → List(T) → Option(T)
firstElem ∅ = Option.None
firstElem (x ⊰ _) = Option.Some(x)

-- The last element of the list
lastElem : ∀{ℓ}{T : Type{ℓ}} → List(T) → Option(T)
lastElem l = foldᵣ (elem ↦ _ ↦ Option.Some(elem)) Option.None l -- TODO: Is this wrong?

_orₗ_ : ∀{ℓ}{T : Type{ℓ}} → List(T) → List(T) → List(T)
_orₗ_ ∅ default = default
_orₗ_ l _ = l

-- Reverse the order of the elements in the list
reverse : ∀{ℓ}{T : Type{ℓ}} → List(T) → List(T)
reverse ∅ = ∅
reverse (x ⊰ l) = (reverse l) ++ (singleton x)

-- The list with an element repeated n times
repeat : ∀{ℓ}{T : Type{ℓ}} → T → ℕ → List(T)
repeat _ 𝟎      = ∅
repeat x (𝐒(n)) = x ⊰ (repeat x n)

-- The list with a list concatenated (repeated) n times
_++^_ : ∀{ℓ}{T : Type{ℓ}} → List(T) → ℕ → List(T)
_++^_ _ 𝟎      = ∅
_++^_ l (𝐒(n)) = l ++ (l ++^ n)

pattern [_ l = l
pattern _] x = x ⊰ ∅

satisfiesAny : ∀{ℓ}{T : Type{ℓ}} → (T → Bool) → List(T) → Bool
satisfiesAny pred ∅       = 𝐹
satisfiesAny pred (x ⊰ l) = pred(x) || satisfiesAny(pred)(l)

satisfiesAll : ∀{ℓ}{T : Type{ℓ}} → (T → Bool) → List(T) → Bool
satisfiesAll pred ∅       = 𝑇
satisfiesAll pred (x ⊰ l) = pred(x) && satisfiesAll(pred)(l)

-- TODO
-- List-apply : ∀{ℓ}{L : List(Type{ℓ})} → (foldᵣ (_⨯_) (Out) (L)) → ∀{Out : Type{ℓ}} → (foldᵣ (_→ᶠ_) (Out) (L)) → Out
-- List-apply(∅)           (f) = f
-- List-apply(head ⊰ rest) (f) = List-apply(rest) (f(head))

-- fn-to-list : ∀{ℓ}{L : List(Type{ℓ})}{Out : Type{ℓ}} → (foldᵣ (_→ᶠ_) (Out) (L)) → (List(Type{ℓ}) → Out)
-- fn-to-list{∅} = 
