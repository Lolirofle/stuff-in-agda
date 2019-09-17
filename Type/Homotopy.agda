module Type.Homotopy where

open import Relator.Equals
open import Type.Dependent
open import Type.Unit

IsLevel : ℕ → Type → Stmt
IsLevel(𝟎)   (A) = IsUnit(A)
IsLevel(𝐒(n))(A) = ∀{x y : A} → IsLevel(n)(x ≡ y)

-- TODO: ComputablyDecidable → UIP (https://homotopytypetheory.org/2012/03/30/a-direct-proof-of-hedbergs-theorem/)
