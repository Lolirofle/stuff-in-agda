module Data.List.Proofs.Simple where

import      Lvl
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data.Boolean.Proofs
import      Data.Option as Option
open import Data.List
open import Data.List.Functions
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Type

private variable ℓ : Lvl.Level
private variable T A B C : Type{ℓ}
private variable f g : A → B
private variable _▫_ : A → B → C
private variable x y : T
private variable l xs ys : List(T)

satisfiesAll₂-step : (satisfiesAll₂(_▫_) f g (x ⊰ xs) (y ⊰ ys)) ≡ (x ▫ y) && (satisfiesAll₂(_▫_) f g xs ys)
satisfiesAll₂-step {_▫_ = _▫_}{x = x}{y = y} with (x ▫ y)
... | 𝑇 = [≡]-intro
... | 𝐹 = [≡]-intro

satisfiesAll-step : (satisfiesAll f (x ⊰ l) ≡ f(x) && (satisfiesAll f l))
satisfiesAll-step {f = f}{x = x} with f(x)
... | 𝑇 = [≡]-intro
... | 𝐹 = [≡]-intro

satisfiesAny₂-step : (satisfiesAny₂(_▫_) f g (x ⊰ xs) (y ⊰ ys)) ≡ (x ▫ y) || (satisfiesAny₂(_▫_) f g xs ys)
satisfiesAny₂-step {_▫_ = _▫_}{x = x}{y = y} with (x ▫ y)
... | 𝑇 = [≡]-intro
... | 𝐹 = [≡]-intro

satisfiesAny-step : (satisfiesAny f (x ⊰ l) ≡ f(x) || (satisfiesAny f l))
satisfiesAny-step {f = f}{x = x} with f(x)
... | 𝑇 = [≡]-intro
... | 𝐹 = [≡]-intro

filterFirst-step : (filterFirst f (x ⊰ l) ≡ if f(x) then l else (x ⊰ filterFirst f l))
filterFirst-step {f = f}{x = x} with f(x)
... | 𝑇 = [≡]-intro
... | 𝐹 = [≡]-intro

find-step : (find f(x ⊰ l) ≡ if f(x) then Option.Some(x) else find f(l))
find-step {f = f}{x = x} with f(x)
... | 𝑇 = [≡]-intro
... | 𝐹 = [≡]-intro
