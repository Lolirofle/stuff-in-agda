open import Formalization.PredicateLogic.Signature

module Formalization.PredicateLogic.Classical.Semantics (𝔏 : Signature) {ℓₘ} where
open Signature(𝔏)

import      Lvl
open import Data.Boolean
open import Data.ListSized
open import Numeral.Natural
open import Type

private variable args : ℕ

-- Model.
-- A model decides which propositional constants that are true or false.
-- A model in a signature `s` consists of a domain and interpretations of the function/relation symbols in `s`.
-- Also called: Structure.
-- Note: A model satisfying `∀{args} → Empty(Prop args)` is called an "Algebraic structure".
record Model : Type{ℓₚ Lvl.⊔ ℓₒ Lvl.⊔ Lvl.𝐒(ℓₘ)} where
  field
    Domain : Type{ℓₘ}                                  -- The type of objects that quantifications quantifies over and functions/relations maps from.
    function : Obj(args) → List(Domain)(args) → Domain -- Maps Obj to a n-ary function (n=0 is interpreted as a constant).
    relation : Prop(args) → List(Domain)(args) → Bool  -- Maps Prop to a boolean n-ary relation (n=0 is interpreted as a proposition).

open Model public using() renaming (Domain to dom ; function to fn ; relation to rel)
