module Data.Tuple.RaiseTypeᵣ.Functions where

open import Data
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Data.Tuple.Raise
import      Data.Tuple.Raiseᵣ.Functions as Raise
open import Data.Tuple.RaiseTypeᵣ
open import Functional
import      Lvl
open import Lvl.MultiFunctions
open import Numeral.Finite
open import Numeral.Natural
open import Numeral.Natural.Relation
open import Syntax.Number
open import Type

from-[^] : ∀{n}{ℓ} → (Type{ℓ} ^ n) → Types(Raise.repeat n ℓ)
from-[^] {0}       <>       = <>
from-[^] {1}       T        = T
from-[^] {𝐒(𝐒(n))} (T , Ts) = (T , from-[^] {𝐒(n)} Ts)

-- Prepends an element to a tuple.
-- Example: a ⊰ (b,c) = (a,b,c)
_⊰_ : ∀{n}{ℓ}{ℓ𝓈} → Type{ℓ} → Types{n}(ℓ𝓈) → Types{𝐒(n)}(ℓ Raise.⊰ ℓ𝓈)
_⊰_ {𝟎}    = const
_⊰_ {𝐒(n)} = _,_

-- The first element of a tuple.
-- Example: head(a,b,c) = a
head : ∀{n} ⦃ pos : Positive(n) ⦄ {ℓ𝓈} → Types{n}(ℓ𝓈) → Type{Raise.head(ℓ𝓈)}
head {1}       = id
head {𝐒(𝐒(_))} = Tuple.left

-- The tuple without its first element.
-- Example: tail(a,b,c) = (b,c)
tail : ∀{n} ⦃ pos : Positive(n) ⦄ {ℓ𝓈} → Types{n}(ℓ𝓈) → Types(Raise.tail{n}(ℓ𝓈))
tail {1}       = const <>
tail {𝐒(𝐒(_))} = Tuple.right

-- Example: map f(a,b,c,d) = (f(a),f(b),f(c),f(d))
map : ∀{n}{ℓ𝓈}{fℓ} → (∀{ℓ} → Type{ℓ} → Type{fℓ(ℓ)}) → (Types{n}(ℓ𝓈) → Types(Raise.map fℓ(ℓ𝓈)))
map{0}       f = const <>
map{1}       f = f
map{𝐒(𝐒(n))} f = Tuple.map f (map{𝐒(n)} f)

-- Example: map₂(_▫_) (a₁,b₁,c₁,d₁) (a₂,b₂,c₂,d₂) = (a₁ ▫ a₂ , b₁ ▫ b₂ , c₁ ▫ c₂ , d₁ ▫ d₂)
map₂ : ∀{n}{ℓ𝓈₁}{ℓ𝓈₂}{fℓ} → (∀{ℓ₁ ℓ₂} → Type{ℓ₁} → Type{ℓ₂} → Type{fℓ ℓ₁ ℓ₂}) → (Types{n}(ℓ𝓈₁) → Types{n}(ℓ𝓈₂) → Types(Raise.map₂ fℓ ℓ𝓈₁ ℓ𝓈₂))
map₂{0}       _ _        _        = <>
map₂{1}       f x        y        = f x y
map₂{𝐒(𝐒(n))} f (x , xs) (y , ys) = (f x y , map₂{𝐒(n)} f xs ys)

mapFromRaise : ∀{n}{ℓ}{T : Type{ℓ}}{fℓ : T → Lvl.Level} → ((x : T) → Type{fℓ(x)}) → ((l : (T ^ n)) → Types(Raise.map fℓ(l)))
mapFromRaise{0}       f _      = <>
mapFromRaise{1}       f(x)     = f(x)
mapFromRaise{𝐒(𝐒(n))} f(x , l) = (f(x) , mapFromRaise{𝐒(n)} f(l))

TypesOfTypes : ∀{n} → (ℓ𝓈 : Lvl.Level ^ n) → Types(Raise.map Lvl.𝐒(ℓ𝓈))
TypesOfTypes = mapFromRaise(\ℓ → Type{ℓ})

-- Similar to map₂ but the second is levels.
-- TODO: This is probably a special case of something?
mapWithLvls : ∀{n}{ℓ𝓈}{fℓ} → (∀{ℓ} → Type{ℓ} → (l : Lvl.Level) → Type{fℓ ℓ l}) → (Types{n}(ℓ𝓈) → (ls : Lvl.Level ^ n) → Types(Raise.map₂ fℓ ℓ𝓈 ls))
mapWithLvls {0}       _ _        _        = <>
mapWithLvls {1}       f x        y        = f x y
mapWithLvls {𝐒(𝐒(n))} f (x , xs) (y , ys) = (f x y , mapWithLvls{𝐒(n)} f xs ys)

-- Returns a element repeated a specified number of times in a tuple
repeat : ∀{ℓ}(n : ℕ) → Type{ℓ} → Types(Raise.repeat n ℓ)
repeat(0)       _ = <>
repeat(1)       x = x
repeat(𝐒(𝐒(n))) x = (x , repeat(𝐒(n)) x)

-- Example: reduceᵣ(_▫_) (a,b,c,d) = a ▫ (b ▫ (c ▫ d))
reduceᵣ : ∀{n}{fℓ}{ℓ𝓈} → (∀{ℓ₁ ℓ₂} → Type{ℓ₁} → Type{ℓ₂} → Type{fℓ ℓ₁ ℓ₂}) → Types{𝐒(n)}(ℓ𝓈) → Type{Raise.reduceᵣ fℓ ℓ𝓈}
reduceᵣ {𝟎}    (_▫_) x        = x
reduceᵣ {𝐒(n)} (_▫_) (x , xs) = x ▫ reduceᵣ {n} (_▫_) xs

-- Example: foldᵣ(_▫_) def (a,b,c,d) = a ▫ (b ▫ (c ▫ (d ▫ def)))
foldᵣ : ∀{n}{fℓ}{ℓ}{ℓ𝓈} → (∀{ℓ₁ ℓ₂} → Type{ℓ₁} → Type{ℓ₂} → Type{fℓ ℓ₁ ℓ₂}) → Type{ℓ} → Types{n}(ℓ𝓈) → Type{Raise.foldᵣ fℓ ℓ ℓ𝓈}
foldᵣ {0}       (_▫_) def _        = def
foldᵣ {1}       (_▫_) def x        = x ▫ def
foldᵣ {𝐒(𝐒(n))} (_▫_) def (x , xs) = x ▫ foldᵣ {𝐒(n)} (_▫_) def xs

-- Example: reduceOrᵣ(_▫_) def (a,b,c,d) = a ▫ (b ▫ (c ▫ d))
reduceOrᵣ : ∀{n}{fℓ}{ℓ}{ℓ𝓈} → (∀{ℓ₁ ℓ₂} → Type{ℓ₁} → Type{ℓ₂} → Type{fℓ ℓ₁ ℓ₂}) → Type{ℓ} → Types{n}(ℓ𝓈) → Type{Raise.reduceOrᵣ fℓ ℓ ℓ𝓈}
reduceOrᵣ {0}       (_▫_) def _        = def
reduceOrᵣ {1}       (_▫_) def x        = x
reduceOrᵣ {𝐒(𝐒(n))} (_▫_) def (x , xs) = x ▫ reduceOrᵣ {𝐒(n)} (_▫_) def xs

-- A tuple with only a single element.
-- Example: singleton(x) = x
singleton : ∀{ℓ} → Type{ℓ} → Types{1}(Raise.singleton ℓ)
singleton = id

-- The element at the specified position of a tuple.
-- Example: index(2)(a,b,c,d) = c
index : ∀{n}{ℓ𝓈} → (i : 𝕟(n)) → Types{n}(ℓ𝓈) → Type{Raise.index i ℓ𝓈}
index {1}       𝟎      = id
index {𝐒(𝐒(_))} 𝟎      = head
index {𝐒(𝐒(n))} (𝐒(i)) = index{𝐒(n)} i ∘ tail

-- The tuple without the element at the specified position.
-- Example: without(2)(a,b,c,d) = (a,b,d)
without : ∀{n}{ℓ𝓈} → (i : 𝕟(𝐒(n))) → Types{𝐒(n)}(ℓ𝓈) → Types{n}(Raise.without i ℓ𝓈)
without{𝟎}    𝟎             = const <>
without{𝐒(n)} 𝟎             = tail
without{𝐒(n)} (𝐒 i) (x , l) = (x ⊰ without{n} i l)

-- Concatenates two tuples.
-- Example: (1,2,3,4) ++ (5,6) = (1,2,3,4,5,6)
_++_ : ∀{a b}{ℓ𝓈₁}{ℓ𝓈₂} → Types{a}(ℓ𝓈₁) → Types{b}(ℓ𝓈₂) → Types(Raise._++_ {a}{b} ℓ𝓈₁ ℓ𝓈₂)
_++_ {0}       _        ys = ys
_++_ {1}       x        ys = x ⊰ ys
_++_ {𝐒(𝐒(a))} (x , xs) ys = x ⊰ (xs ++ ys)
