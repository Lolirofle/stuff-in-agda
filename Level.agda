module Level where

open import Agda.Primitive public
  using (Level; _⊔_)
  renaming (lzero to zero; lsuc to suc)
