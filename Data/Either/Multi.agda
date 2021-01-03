module Data.Either.Multi where

open import Data
open import Data.Either
import      Data.Tuple.Raiseᵣ.Functions as Raise
open import Data.Tuple.RaiseTypeᵣ
open import Data.Tuple.RaiseTypeᵣ.Functions
open import Data.Tuple using (_⨯_ ; _,_)
open import Function.Multi
open import Function.Multi.Functions
import      Lvl
import      Lvl.MultiFunctions as Lvl
open import Numeral.Finite
open import Numeral.Natural
open import Type

Alt : (n : ℕ) → ∀{ℓ𝓈} → TypesOfTypes{n}(ℓ𝓈) ⇉ Type{Lvl.⨆(ℓ𝓈)}
Alt(n) = binaryTypeRelator₊(n)(_‖_)(Empty)

pattern alt₀   x = _‖_.Left x
pattern alt₁   x = _‖_.Right(alt₀ x)
pattern alt₂   x = _‖_.Right(alt₁ x)
pattern alt₃   x = _‖_.Right(alt₂ x)
pattern alt₄   x = _‖_.Right(alt₃ x)
pattern alt₅   x = _‖_.Right(alt₄ x)
pattern alt₆   x = _‖_.Right(alt₅ x)
pattern alt₇   x = _‖_.Right(alt₆ x)
pattern alt₈   x = _‖_.Right(alt₇ x)
pattern alt₉   x = _‖_.Right(alt₈ x)
pattern alt₁,₂ x = _‖_.Right(x)
pattern alt₂,₃ x = _‖_.Right(alt₁,₂ x)
pattern alt₃,₄ x = _‖_.Right(alt₂,₃ x)
pattern alt₄,₅ x = _‖_.Right(alt₃,₄ x)
pattern alt₅,₆ x = _‖_.Right(alt₄,₅ x)
pattern alt₆,₇ x = _‖_.Right(alt₅,₆ x)
pattern alt₇,₈ x = _‖_.Right(alt₆,₇ x)
pattern alt₈,₉ x = _‖_.Right(alt₇,₈ x)

{-
-- TODO: Move or generalize uncurry
uncurryTypes : (n : ℕ) → ∀{ℓ𝓈}{ℓ}{B : Type{ℓ}} → (TypesOfTypes{𝐒(n)}(ℓ𝓈) ⇉ B) → (Types(ℓ𝓈) → B)
uncurryTypes(𝟎)    f          = f
uncurryTypes(𝐒(n)) f (x , xs) = uncurryTypes(n) (f(x)) xs

-- TODO: Problem with the type. Not normalizing correctly
alt : ∀{n}{ℓ𝓈}{As : Types(ℓ𝓈)} → (i : 𝕟(𝐒(n))) → (index i As) → uncurryTypes(n) (Alt(𝐒(n)){ℓ𝓈}) As
alt {0}       𝟎     x = x
alt {1}       𝟎     x = Left  x
alt {1}       (𝐒 𝟎) x = Right x
alt {𝐒(𝐒(n))} 𝟎     x = {!Left x!}
alt {𝐒(𝐒(n))} (𝐒 i) x = {!Right(alt {𝐒(n)} i x)!}
-}
