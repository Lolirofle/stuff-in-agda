module Miscellaneous.InstanceLoop where

open import Type

postulate A : TYPE
postulate B : TYPE
postulate C : TYPE

instance
  postulate ab : ⦃ A ⦄ → B

instance
  postulate ba : ⦃ B ⦄ → A

postulate a : A

test-a : B
test-a = ab
