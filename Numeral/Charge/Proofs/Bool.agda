module Numeral.Charge.Proofs.Bool where

open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data.Boolean.Stmt
open import Data.Boolean.Stmt.Logic
open import Functional
open import Numeral.Charge

elim₃-implication : ∀{s}{a₁ a₂ a₃ b₁ b₂ b₃} → IsTrue(a₁ →? b₁) → IsTrue(a₂ →? b₂) → IsTrue(a₃ →? b₃) → IsTrue(elim₃ a₁ a₂ a₃ s →? elim₃ b₁ b₂ b₃ s)
elim₃-implication {➕} _ _ t = t
elim₃-implication {𝟎}  _ t _ = t
elim₃-implication {➖} t _ _ = t

elim₃-sub : ∀{s}{a₁ a₂ a₃ b₁ b₂ b₃} → IsTrue(a₁ →? b₁) → IsTrue(a₂ →? b₂) → IsTrue(a₃ →? b₃) → IsTrue(elim₃ a₁ a₂ a₃ s) → IsTrue(elim₃ b₁ b₂ b₃ s)
elim₃-sub = IsTrue.[→?]-elim ∘₃ elim₃-implication
