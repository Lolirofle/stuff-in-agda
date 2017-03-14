module Type where

module Level where
  open import Agda.Primitive public
    using    (Level; _⊔_)
    renaming (lzero to 𝟎; lsuc to 𝐒)

open Level using (Level) public


Type : _
Type = Set

TypeN : (_ : Level) → _
TypeN n = Set n

data ⊥ {n} : TypeN n where

record Unit {n} : TypeN n where

{-# BUILTIN UNIT Unit #-}
-- {-# COMPILED_DATA Unit () () #-}
