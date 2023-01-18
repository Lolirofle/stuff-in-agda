module Dataω.Tuple where

open import Typeω.Dependent.Sigma
open import Type

_⨯_ : Typeω → Typeω → Typeω
A ⨯ B = Σ A (\_ → B)

open Typeω.Dependent.Sigma public
  using()
  renaming (module Σ to _⨯_ ; intro to _,_)

open _⨯_ public
