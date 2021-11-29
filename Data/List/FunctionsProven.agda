-- Note that an alternative to these functions is to use a list of sigma types instead.
module Data.List.FunctionsProven where

import      Lvl
open import Data.Boolean
open import Data.List as List using (List ; ∅ ; _⊰_)
import      Data.List.Functions as List
open import Data.List.Relation.Membership
open import Data.List.Relation.Quantification
open import Functional
open import Functional.Instance
open import Syntax.Function
open import Type

private variable ℓ : Lvl.Level
private variable A B T Result : Type{ℓ}
private variable P : T → Type{ℓ}

foldₗ : (Result → (x : T) → P(x) → Result) → Result → (l : List(T)) → AllElements(P)(l) → Result
foldₗ f result ∅       ∅         = result
foldₗ f result (x ⊰ l) (px ⊰ pl) = foldₗ f (f result x px) l pl

foldᵣ : ((x : T) → P(x) → Result → Result) → Result → (l : List(T)) → AllElements(P)(l) → Result
foldᵣ f init ∅       ∅         = init
foldᵣ f init (x ⊰ l) (px ⊰ pl) = f x px (foldᵣ f init l pl)

map : ((x : A) → P(x) → B) → ((l : List(A)) → AllElements(P)(l) → List(B))
map f ∅       ∅         = ∅
map f (x ⊰ l) (px ⊰ pl) = (f x px) ⊰ (map f l pl)

filter : ((x : T) → P(x) → Bool) → ((l : List(T)) → AllElements(P)(l) → List(T))
filter f ∅       ∅         = ∅
filter f (x ⊰ l) (px ⊰ pl) = (if(f(x) px) then (x List.⊰_) else id) (filter f l pl)
