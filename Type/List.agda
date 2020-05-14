module Type.List where

open import Data
open import Data.Tuple
open import Data.Tuple.Raise
import      Data.Tuple.Raiseᵣ.Functions as Raise
open import Lvl using (Level)
open import Lvl.List
open import Numeral.Natural
open import Type

Types : ∀{n} → (ℓ𝓈 : (Level ^ n)) → Type{Lvl.𝐒(⨆{n} ℓ𝓈)}
Types {𝟎}       _       = Unit
Types {𝐒(𝟎)}    ℓ       = Type{ℓ}
Types {𝐒(𝐒(n))} (ℓ , ℓ𝓈) = Type{ℓ} ⨯ Types{𝐒(n)}(ℓ𝓈)
-- TODO: Not sure what the problem with this is: Types {n} ℓ𝓈 = Raise.Dependent.foldᵣ {A = Level} ℓ𝓈 {B = \ℓ𝓈₂ → {!Type{Lvl.𝐒(⨆{n} ℓ𝓈₂)}!}} {!(\ℓ → Type{ℓ} ⨯_)!} Unit
