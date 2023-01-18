module Syntax.Existential where

import Logic.Predicate

open Logic.Predicate
  using ()
  renaming ([∃]-intro to ⱻ ; [∃]-witness to ◦ ; [∃]-proof to ⦾)
  public
