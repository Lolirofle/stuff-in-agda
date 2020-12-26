module Data.Boolean where

import Lvl
open import Type

-- Boolean type
data Bool : Type{Lvl.𝟎} where
  𝑇 : Bool -- Represents truth
  𝐹 : Bool -- Represents falsity

{-# BUILTIN BOOL  Bool #-}
{-# BUILTIN TRUE  𝑇 #-}
{-# BUILTIN FALSE 𝐹 #-}

elim : ∀{ℓ}{T : Bool → Type{ℓ}} → T(𝑇) → T(𝐹) → ((b : Bool) → T(b))
elim t _ 𝑇 = t
elim _ f 𝐹 = f

not : Bool → Bool
not 𝑇 = 𝐹
not 𝐹 = 𝑇
{-# COMPILE GHC not = not #-}

-- Control-flow if-else expression
if_then_else_ : ∀{ℓ}{T : Type{ℓ}} → Bool → T → T → T
if b then t else f = elim t f b
