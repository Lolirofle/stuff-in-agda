module Formalization.LambdaCalculus.ByVarCount.ByLevels.Terms.ApplyIterated where

open import Formalization.LambdaCalculus.ByVarCount
open import Formalization.LambdaCalculus.ByVarCount.Syntax.ExplicitLambda
open import Numeral.Natural as ℕ using (ℕ)

ApplyIterated : ∀{d} → Term(d) → Term(d) → ℕ → Term(d)
ApplyIterated f x ℕ.𝟎      = x
ApplyIterated f x (ℕ.𝐒(n)) = f ← ApplyIterated f x n

module Proofs where
  open import Data
  open import Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Reduction
  open import Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Reduction.Proofs
  open import Formalization.LambdaCalculus.ByVarCount.Functions renaming (varShift𝐒ᵢ to _↑ᵢ ; varShift𝐒Outermost to _↑')
  open import Formalization.LambdaCalculus.ByVarCount.Functions.Proofs
  open import Numeral.Finite as 𝕟 using (𝕟)
  open import Numeral.Natural.Oper
  open import Numeral.Natural.Oper.Proofs
  open import Relator.Equals
  open import Relator.Equals.Proofs.Equiv
  open import Structure.Function
  open import Structure.Operator
  open import Structure.Relator.Properties
  open import Syntax.Transitivity

  private variable n n₁ n₂ : ℕ
  private variable i : 𝕟(n)
  private variable f g h t x y z f₁ f₂ x₁ x₂ : Term(n)

  instance
    [⇴]-ApplyIterated-compatibleᵣ : Compatible₁(_⇴_)(_⇴_)(\x → ApplyIterated f x n)
    Compatible₁.proof ([⇴]-ApplyIterated-compatibleᵣ {n = ℕ.𝟎})   p = p
    Compatible₁.proof ([⇴]-ApplyIterated-compatibleᵣ {n = ℕ.𝐒 n}) p = cong-applyᵣ(Compatible₁.proof ([⇴]-ApplyIterated-compatibleᵣ {n = n}) p)

  [⇴*]-ApplyIteratedₗ-function : Compatible₁(_⇴*_)(_⇴*_)(\f → ApplyIterated f x n)
  Compatible₁.proof ([⇴*]-ApplyIteratedₗ-function {n = ℕ.𝟎})   p = reflexivity(_⇴*_)
  Compatible₁.proof ([⇴*]-ApplyIteratedₗ-function {n = ℕ.𝐒 n}) p = compatible₁(_⇴*_)(_⇴*_)(_← _) p 🝖 compatible₁(_⇴*_)(_⇴*_)(_ ←_) (Compatible₁.proof ([⇴*]-ApplyIteratedₗ-function {n = n}) p)

  [⇴*]-ApplyIteratedᵣ-function : Compatible₁(_⇴*_)(_⇴*_)(\x → ApplyIterated f x n)
  [⇴*]-ApplyIteratedᵣ-function = [⇴*]-super-function

  [⇴*]-ApplyIterated-function : (f₁ ⇴* f₂) → (x₁ ⇴* x₂) → (ApplyIterated f₁ x₁ n ⇴* ApplyIterated f₂ x₂ n)
  [⇴*]-ApplyIterated-function {n = n} pf px = Compatible₁.proof ([⇴*]-ApplyIteratedₗ-function {n = n}) pf 🝖 Compatible₁.proof [⇴*]-ApplyIteratedᵣ-function px

  substituteVar-on-ApplyIterated : substituteVar i t (ApplyIterated f x n) ≡ ApplyIterated (substituteVar i t f) (substituteVar i t x) n
  substituteVar-on-ApplyIterated {n = ℕ.𝟎} = [≡]-intro
  substituteVar-on-ApplyIterated {i = i}{t = t}{f = f}{x = x}{n = ℕ.𝐒 n}
    rewrite substituteVar-on-ApplyIterated {i = i}{t = t}{f = f}{x = x}{n = n}
    = [≡]-intro
  {-# REWRITE substituteVar-on-ApplyIterated #-}

  varShift𝐒-on-ApplyIterated : varShift𝐒 i (ApplyIterated f x n) ≡ ApplyIterated (varShift𝐒 i f) (varShift𝐒 i x) n
  varShift𝐒-on-ApplyIterated {n = ℕ.𝟎} = [≡]-intro
  varShift𝐒-on-ApplyIterated {i = i}{f = f}{x = x}{n = ℕ.𝐒 n}
    rewrite varShift𝐒-on-ApplyIterated {i = i}{f = f}{x = x}{n = n}
    = [≡]-intro
  {-# REWRITE varShift𝐒-on-ApplyIterated #-}

  ApplyIterated-[+] : ApplyIterated f (ApplyIterated f x n₁) n₂ ≡ ApplyIterated f x (n₁ + n₂)
  ApplyIterated-[+] {n₂ = ℕ.𝟎} = [≡]-intro
  ApplyIterated-[+] {f = f}{x = x}{n₁ = n₁}{n₂ = ℕ.𝐒 n₂}
    rewrite ApplyIterated-[+] {f = f}{x = x}{n₁ = n₁}{n₂ = n₂}
    = [≡]-intro

  open import Logic.Propositional using ([∨]-introₗ ; [∨]-introᵣ)

  ApplyIterated-[⋅] : ApplyIterated(𝜆 n (ApplyIterated(varShift𝐒 𝕟.maximum f) (Var 𝕟.maximum) n₂)) x n₁ ⇴* ApplyIterated{n} f x (n₁ ⋅ n₂)
  ApplyIterated-[⋅] {n₁ = ℕ.𝟎} = reflexivity(_⇴*_)
  ApplyIterated-[⋅] {n = n}{f = f}{n₂ = n₂}{x = x}{n₁ = ℕ.𝐒 n₁} = let i = 𝕟.maximum in
    ApplyIterated(𝜆 n (ApplyIterated (varShift𝐒 i f) (Var 𝕟.maximum) n₂)) x (ℕ.𝐒(n₁)) 🝖[ _⇴*_ ]-[]
    (𝜆 n (ApplyIterated (varShift𝐒 i f) (Var 𝕟.maximum) n₂))
      ← ApplyIterated(𝜆 n (ApplyIterated (varShift𝐒 i f) (Var 𝕟.maximum) n₂)) x n₁    🝖[ _⇴*_ ]-[ compatible₁(_⇴*_)(_⇴*_)(Apply _) (ApplyIterated-[⋅] {n = n}{f = f}{n₂ = n₂}{x = x}{n₁ = n₁}) ]
    (𝜆 n (ApplyIterated (varShift𝐒 i f) (Var 𝕟.maximum) n₂))
      ← ApplyIterated{n} f x (n₁ ⋅ n₂)                                                🝖[ _⇴_ ]-[ β ]-sub
    ApplyIterated
      (substituteVar 𝕟.maximum (ApplyIterated f x (n₁ ⋅ n₂)) (varShift𝐒 i f))
      (substituteVar 𝕟.maximum (ApplyIterated f x (n₁ ⋅ n₂)) (Var 𝕟.maximum))
      n₂                                                                              🝖[ _⇴*_ ]-[ sub₂(_≡_)(_⇴*_) (congruence₂(\x y → ApplyIterated x y n₂) [≡]-intro substituteVar-identity) ]
    ApplyIterated f (ApplyIterated{n} f x (n₁ ⋅ n₂)) n₂                               🝖[ _⇴*_ ]-[ sub₂(_≡_)(_⇴*_) (ApplyIterated-[+] {f = f}{x = x}{n₁ = n₁ ⋅ n₂}{n₂ = n₂}) ]
    (ApplyIterated{n} f x ((n₁ ⋅ n₂) + n₂))                                           🝖[ _⇴*_ ]-[ sub₂(_≡_)(_⇴*_) (symmetry(_≡_) (congruence₁(ApplyIterated f x) ([⋅]-with-[𝐒]ₗ {x = n₁}{y = n₂}))) ]
    ApplyIterated f x (ℕ.𝐒(n₁) ⋅ n₂) 🝖-end
