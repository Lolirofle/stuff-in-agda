module Data.Either.Proofs where

import      Lvl
open import Data
open import Data.Boolean
open import Data.Boolean.Proofs
open import Data.Boolean.Stmt
open import Data.Either as Either
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑ₄ ℓₑ₅ ℓₑ₆ : Lvl.Level
private variable T A B C A₁ A₂ A₃ B₁ B₂ B₃ : Type{ℓ}
private variable P : T → Type{ℓ}
private variable a : A
private variable b : B

isLeft-correctness : (e : (A ‖ B)) → IsTrue(Either.isLeft(e)) → A
isLeft-correctness (Left a) _ = a

isRight-correctness : (e : (A ‖ B)) → IsTrue(Either.isRight(e)) → B
isRight-correctness (Right b) _ = b

either-elim-if-isLeft : let _ = P in (A → P(a)) → (B → P(b)) → (e : A ‖ B) → P(if(Either.isLeft e) then a else b)
either-elim-if-isLeft = Either.elim _

either-elim-if-isRight : let _ = P in (A → P(a)) → (B → P(b)) → (e : A ‖ B) → P(if(Either.isRight e) then b else a)
either-elim-if-isRight = Either.elim _
