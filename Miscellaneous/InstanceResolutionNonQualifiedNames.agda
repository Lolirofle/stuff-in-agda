module Miscellaneous.InstanceResolutionNonQualifiedNames where

-- https://agda.readthedocs.io/en/latest/language/instance-arguments.html#instance-resolution
-- "Verify the goal: First we check that the goal type has the right shape to be solved by instance resolution. It should be of the form {Γ} → C vs, where the target type C is a variable from the context or the name of a data or record type"

import      Lvl
open import Type

postulate P : ∀{ℓ} → TYPE ℓ → TYPE ℓ
postulate T : TYPE
postulate F : T → TYPE

-- Resolves an instance.
lookup : ∀{ℓ}{T : Type{ℓ}} →  ⦃ T ⦄ → T
lookup ⦃ t ⦄ = t

------------------------------------------------------------
-- Works when wrapped in a name P.

instance postulate _ : P(T)
pt : P(T)
pt = lookup

instance postulate _ : P(T → T)
ptt : P(T → T)
ptt = lookup

instance postulate _ : P((t : T) → F(t))
ptft : P((t : T) → F(t))
ptft = lookup

instance postulate _ : P(TYPE)
pty : P(TYPE)
pty = lookup

------------------------------------------------------------
-- Different behaviour without the name P.

-- This is OK, as expected.
instance postulate _ : T
t : T
t = lookup

{-
-- I guess this is intended to not work, but why not? Is there a reason for "→" to not behave like a name?
instance postulate _ : T → T -- Instance declarations with explicit arguments are never considered by instance search
tt : T → T
tt = lookup -- Instance search cannot be used to find elements in an explicit function type
-}

{-
-- It is the same with dependent explicit function types.
instance postulate _ : (t : T) → F(t) -- "Instance declarations with explicit arguments are never considered by instance search"
tft : (t : T) → F(t)
tft = lookup  -- "Instance search cannot be used to find elements in an explicit function type"
-}

{-
-- Not really useful? But it shows another kind of term that instance search don't work with.
instance postulate _ : TYPE -- "Terms marked as eligible for instance search should end with a name"
ty : TYPE
ty = lookup -- "Instance search can only be used to find elements in a named type"
-}

-- https://github.com/agda/agda/issues/3702
-- https://github.com/agda/agda/issues/3534



{-
instance postulate _ : P({t : T} → F(t))
ptit : P({t : T} → F(t))
ptit = lookup

instance postulate i : {t : T} → F(t)
tit : {t : T} → F(t)
tit = lookup
-}
