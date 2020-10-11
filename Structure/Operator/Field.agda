module Structure.Operator.Field where

import      Lvl
open import Logic
open import Logic.Propositional
open import Structure.Setoid.WithLvl
open import Structure.Operator.Properties
open import Structure.Operator.Ring
open import Type

record Field {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) : Stmt{ℓ Lvl.⊔ ℓₑ} where
  field
    ⦃ ring ⦄              : Ring(_+_)(_⋅_)
    ⦃ unity ⦄             : Unity(_+_)(_⋅_)
    ⦃ divisionRing ⦄      : DivisionRing(_+_)(_⋅_)
    ⦃ [⋅]-commutativity ⦄ : Commutativity(_⋅_)

  open Ring(ring) public
  open Unity(unity) public
  open DivisionRing(divisionRing) public

  field
     -- Note: This excludes the trivial ring and is unprovable from the other field axioms, and models where this is true are always a "trivial/singleton ring".
    distinct-identities : (𝟎 ≢ 𝟏)
