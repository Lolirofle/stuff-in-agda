module List where

open import Boolean
import      Boolean.Operators
open        Boolean.Operators.Programming
open import Data
open import Functional
import      Level as Lvl
open import Logic.Propositional
open import Numeral.Natural
open import Type

infixl 1000 _⊱_ _++_
infixr 1000 _⊰_
infixl 1      [_
infixl 100000 _]

data List {lvl} (T : Type{lvl}) : Type{lvl} where
  ∅ : List(T)
  _⊰_ : T → List(T) → List(T)

_⊱_ : ∀{lvl}{T : Type{lvl}} → List(T) → T → List(T)
_⊱_ ∅ b = b ⊰ ∅
_⊱_ (elem ⊰ rest) b = elem ⊰ (rest ⊱ elem)

_++_ : ∀{lvl}{T : Type{lvl}} → List(T) → List(T) → List(T)
_++_ ∅ b = b
_++_ (elem ⊰ rest) b = elem ⊰ (rest ++ b)

pattern empty = ∅
pattern prepend elem list = elem ⊰ list
postpend = _⊱_
concat   = _++_

singleton : ∀{lvl}{T : Type{lvl}} → T → List(T)
singleton elem = elem ⊰ ∅

tail : ∀{lvl}{T : Type{lvl}} → List(T) → List(T)
tail ∅ = ∅
tail (_ ⊰ l) = l

map : ∀{lvl₁ lvl₂}{T₁ : Type{lvl₁}}{T₂ : Type{lvl₂}} → (T₁ → T₂) → List(T₁) → List(T₂)
map _ ∅ = ∅
map f (elem ⊰ l) = (f elem) ⊰ (map f l)

foldₗ : ∀{lvl₁ lvl₂}{T : Type{lvl₁}}{Result : Type{lvl₂}} → (Result → T → Result) → Result → List(T) → Result
foldₗ _   result ∅ = result
foldₗ _▫_ result (elem ⊰ l) = foldₗ _▫_ (result ▫ elem) l

foldᵣ : ∀{lvl₁ lvl₂}{T : Type{lvl₁}}{Result : Type{lvl₂}} → (T → Result → Result) → Result → List(T) → Result
foldᵣ _   init ∅ = init
foldᵣ _▫_ init (elem ⊰ l) = elem ▫ (foldᵣ _▫_ init l)

reduceOrᵣ : ∀{lvl}{T : Type{lvl}} → (T → T → T) → T → List(T) → T
reduceOrᵣ _   init ∅ = init
reduceOrᵣ _▫_ init (elem ⊰ ∅) = elem
reduceOrᵣ _▫_ init (elem₁ ⊰ (elem₂ ⊰ l)) = elem₁ ▫ (reduceOrᵣ _▫_ init (elem₂ ⊰  l))

index : ∀{lvl}{T : Type{lvl}} → ℕ → List(T) → Option(T)
index _      ∅       = Option.None
index 𝟎      (x ⊰ _) = Option.Some(x)
index (𝐒(n)) (_ ⊰ l) = index n l

first : ∀{lvl}{T : Type{lvl}} → ℕ → List(T) → List(T)
first _      ∅       = ∅
first 𝟎      (x ⊰ _) = x ⊰ ∅
first (𝐒(n)) (x ⊰ l) = x ⊰ (first n l)

length : ∀{lvl}{T : Type{lvl}} → List(T) → ℕ
length ∅ = 𝟎
length (_ ⊰ l) = 𝐒(length l)
-- foldᵣ (_ count ↦ 𝐒(count)) 0 l

mapWindow2ₗ : ∀{lvl}{T : Type{lvl}} → (T → T → T) → List(T) → List(T)
mapWindow2ₗ f (x₁ ⊰ x₂ ⊰ l) = (f x₁ x₂) ⊰ (mapWindow2ₗ f (x₂ ⊰ l))
mapWindow2ₗ _ _ = ∅

firstElem : ∀{lvl}{T : Type{lvl}} → List(T) → Option(T)
firstElem ∅ = Option.None
firstElem (x ⊰ _) = Option.Some(x)

lastElem : ∀{lvl}{T : Type{lvl}} → List(T) → Option(T)
lastElem l = foldᵣ (elem ↦ _ ↦ Option.Some(elem)) Option.None l -- TODO: Is this wrong?

_or_ : ∀{lvl}{T : Type{lvl}} → List(T) → List(T) → List(T)
_or_ ∅ default = default
_or_ l _ = l

reverse : ∀{lvl}{T : Type{lvl}} → List(T) → List(T)
reverse ∅ = ∅
reverse (x ⊰ l) = (reverse l) ++ (singleton x)

repeat : ∀{lvl}{T : Type{lvl}} → T → ℕ → List(T)
repeat _ 𝟎      = ∅
repeat x (𝐒(n)) = x ⊰ (repeat x n)

multiply : ∀{lvl}{T : Type{lvl}} → List(T) → ℕ → List(T)
multiply _ 𝟎      = ∅
multiply l (𝐒(n)) = l ++ (multiply l n)

List-induction : ∀{l₁ l₂}{T : Type{l₁}}{P : List(T) → Stmt{l₁ Lvl.⊔ l₂}} → P(∅) → (∀(x : T)(l : List(T)) → P(l) → P(x ⊰ l)) → (∀{l : List(T)} → P(l))
List-induction          base next {∅} = base
List-induction {l₁}{l₂} base next {x ⊰ l} = next(x)(l)(List-induction {l₁}{l₂} base next {l})

pattern [_ l = l
pattern _] x = x ⊰ ∅

any : ∀{lvl}{T : Type{lvl}} → (T → Bool{lvl}) → List(T) → Bool
any pred ∅       = 𝐹
any pred (x ⊰ l) = pred(x) || any(pred)(l)

all : ∀{lvl}{T : Type{lvl}} → (T → Bool{lvl}) → List(T) → Bool
all pred ∅       = 𝑇
all pred (x ⊰ l) = pred(x) && any(pred)(l)
