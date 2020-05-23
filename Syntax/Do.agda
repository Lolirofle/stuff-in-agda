-- Haskell-like do-notation.
module Syntax.Do where

open import Functional
import      Lvl
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable A B : Type{ℓ}
private variable F : Type{ℓ₁} → Type{ℓ₂}

record DoNotation (F : Type{ℓ₁} → Type{ℓ₂}) : Type{Lvl.𝐒(ℓ₁) Lvl.⊔ ℓ₂} where
  constructor intro
  field
    return : A → F(A)
    _>>=_  : F(A) → (A → F(B)) → F(B)

  module HaskellNames where
    _=<<_ : ∀{A B} → (A → F(B)) → F(A) → F(B)
    _=<<_ = swap(_>>=_)

    _>>_ : ∀{A B} → F(A) → F(B) → F(B)
    f >> g = f >>= const g

    _>=>_ : ∀{A B C : Type} → (A → F(B)) → (B → F(C)) → (A → F(C))
    (f >=> g)(A) = f(A) >>= g

    _<=<_ : ∀{A B C : Type} → (B → F(C)) → (A → F(B)) → (A → F(C))
    _<=<_ = swap(_>=>_)

  module IdiomBrackets where
    pure : (A → F(A))
    pure = return

    _<*>_ : F(A → B) → (F(A) → F(B))
    _<*>_ Ff Fa = do
      f <- Ff
      a <- Fa
      return(f(a))

open DoNotation ⦃ … ⦄ using (return ; _>>=_) public
