module Numeral.Integer.Proofs{ℓ} where

import      Lvl
open import Functional
open import Numeral.Integer
open import Numeral.Integer.Oper
open import Numeral.Natural.Induction
open import Numeral.Natural as ℕ using (ℕ)
open import Numeral.Natural.UnclosedOper using () renaming (_−_ to _−ₙ_ ; signed to signedℕ)
open import Numeral.Natural.Oper using () renaming (_+_ to _+ₙ_ ; _⋅_ to _⋅ₙ_)
import      Numeral.Natural.Oper.Proofs as ℕ
open import Logic.Propositional{ℓ}
open import Logic.Predicate{ℓ}{Lvl.𝟎}
open import Relator.Equals{ℓ}{Lvl.𝟎}
open import Relator.Equals.Proofs{ℓ}{Lvl.𝟎}
open import Structure.Function.Domain{ℓ}
open import Structure.Operator.Properties{ℓ}{Lvl.𝟎}
open import Structure.Relator.Properties{ℓ}{Lvl.𝟎}
open import Syntax.Number
open import Syntax.Transitivity

-- TODO: Prove the usual strcutures for ℤ

-- TODO: Is this useful? Unnecessary?
{-
[ℕ][ℤ]-property : (ℕ → Stmt) → (ℤ → Stmt) → Stmt
[ℕ][ℤ]-property (φn) (φz) = (∀{n} → φn(n) ↔ (φz(+ₙ n) ∧ φz(−ₙ n)))

proof-from-[ℕ]₊ : ∀{φ : ℕ → Stmt}{n : ℕ} → ?
-}

[𝐒]-preserving : Preserving(from-ℕ) (ℕ.𝐒) (𝐒)
[𝐒]-preserving = [≡]-intro

[+]-preserving : Preserving2(from-ℕ) (_+ₙ_) (_+_)
[+]-preserving = [≡]-intro

[⋅]-preserving : Preserving2(from-ℕ) (_⋅ₙ_) (_⋅_)
[⋅]-preserving = [≡]-intro

-- [/₀]-preserving : Preserving2(from-ℕ) (_/₀ₙ_) (_/₀_)

-- (−(n+1))−1 = −((n+1)+1)
[𝐏]-negative-successor : ∀{n} → (𝐏(−𝐒ₙ(n)) ≡ −𝐒ₙ(ℕ.𝐒(n)))
[𝐏]-negative-successor = [≡]-intro
  {-
  [ℕ]-induction base next where
    base : (𝐏(−𝐒ₙ(ℕ.𝟎)) ≡ −𝐒ₙ(ℕ.𝐒(ℕ.𝟎)))
    base = [≡]-intro

    next : (n : ℕ) → (𝐏(−𝐒ₙ(n)) ≡ −𝐒ₙ(ℕ.𝐒(n))) → (𝐏(−𝐒ₙ(ℕ.𝐒(n))) ≡ −𝐒ₙ(ℕ.𝐒(ℕ.𝐒(n))))
    next(n)(proof) = congruence₁(𝐏) (proof)
  -}

-- -(n+1) = −(n+1)
[−𝐒ₙ]-identity : ∀{n} → (−𝐒ₙ(n) ≡ −ₙ(ℕ.𝐒(n)))
[−𝐒ₙ]-identity = [≡]-intro
  {-
  [ℕ]-induction base next where
    base : (−𝐒ₙ(ℕ.𝟎) ≡ −ₙ(ℕ.𝐒(ℕ.𝟎)))
    base = [≡]-intro

    postulate next : (n : ℕ) → (−𝐒ₙ(n) ≡ −ₙ(ℕ.𝐒(n))) → (−𝐒ₙ(ℕ.𝐒(n)) ≡ −ₙ(ℕ.𝐒(ℕ.𝐒(n))))
    -- next(n)(proof) = congruence₁(𝐏) (proof)
    -- −𝐒ₙ(n) ≡ −ₙ(ℕ.𝐒(n))
    -- 𝐏(−𝐒ₙ(n)) ≡ 𝐏(−ₙ(ℕ.𝐒(n)))
    -- −𝐒ₙ(ℕ.𝐒(n))) ≡ 𝐏(−𝐒ₙ(n)) ≡ 𝐏(−ₙ(ℕ.𝐒(n)))
    -- −𝐒ₙ(ℕ.𝐒(n))) ≡ 𝐏(−ₙ(ℕ.𝐒(n)))
  -}

-- (−n)−1 = −(n+1)
[𝐏]-negative : ∀{n} → (𝐏(−ₙ n) ≡ −𝐒ₙ(n))
[𝐏]-negative {ℕ.𝟎}    = [≡]-intro
[𝐏]-negative {ℕ.𝐒(n)} = [≡]-intro
{-# REWRITE [𝐏]-negative #-}
  {-
  𝐏(−ₙ ℕ.𝟎)
  = 𝐏(+ₙ ℕ.𝟎)
  = 𝐏(𝟎)
  = −𝐒ₙ(ℕ.𝟎)

  𝐏(−ₙ(ℕ.𝐒(n)))
  = 𝐏(−𝐒ₙ(n))
  = −𝐒ₙ(ℕ.𝐒(n))
  -}

-- (−n)−1−1 = (−(n+1))−1
[𝐏𝐏]-negative : ∀{n} → (𝐏(𝐏(−ₙ n)) ≡ 𝐏(−ₙ(ℕ.𝐒(n))))
[𝐏𝐏]-negative = [≡]-intro

-- (−(n+1))+1 = −n
[𝐒][−𝐒ₙ]-negative-identity : ∀{n} → (𝐒(−𝐒ₙ(n)) ≡ −ₙ n)
[𝐒][−𝐒ₙ]-negative-identity {ℕ.𝟎}    = [≡]-intro
[𝐒][−𝐒ₙ]-negative-identity {ℕ.𝐒(n)} = [≡]-intro

-- (n+1)−1 = n
[𝐏][𝐒]-identity : ∀{n} → (𝐏(𝐒(n)) ≡ n)
[𝐏][𝐒]-identity {𝟎}           = [≡]-intro
[𝐏][𝐒]-identity {+𝐒ₙ(n)}      = [≡]-intro
[𝐏][𝐒]-identity {−𝐒ₙ(ℕ.𝟎)}    = [≡]-intro
[𝐏][𝐒]-identity {−𝐒ₙ(ℕ.𝐒(_))} = [≡]-intro
{-# REWRITE [𝐏][𝐒]-identity #-}

-- (n−1)+1 = n
[𝐒][𝐏]-identity : ∀{n} → (𝐒(𝐏(n)) ≡ n)
[𝐒][𝐏]-identity {𝟎}           = [≡]-intro
[𝐒][𝐏]-identity {+𝐒ₙ(n)}      = [≡]-intro
[𝐒][𝐏]-identity {−𝐒ₙ(ℕ.𝟎)}    = [≡]-intro
[𝐒][𝐏]-identity {−𝐒ₙ(ℕ.𝐒(_))} = [≡]-intro
{-# REWRITE [𝐒][𝐏]-identity #-}

-- An intuitive induction proof method on integers
record [ℤ]-simple-induction-data (P : ℤ → Stmt) : Set(ℓ) where
  constructor [ℤ]-simple-ind
  field
    [−] : ∀{n} → P(−ₙ n) → P(−𝐒ₙ(n))
    [0] : P(𝟎)
    [+] : ∀{n} → P(+ₙ n) → P(+𝐒ₙ(n))

[ℤ]-simple-induction : ∀{P} → [ℤ]-simple-induction-data(P) → (∀{n} → P(n))
[ℤ]-simple-induction {_} ([ℤ]-simple-ind [−] [0] [+]) {𝟎}           = [0]
[ℤ]-simple-induction {P} ([ℤ]-simple-ind [−] [0] [+]) {+𝐒ₙ(n)}      = [+] ([ℤ]-simple-induction {P} ([ℤ]-simple-ind [−] [0] [+]) {+ₙ n})
[ℤ]-simple-induction {P} ([ℤ]-simple-ind [−] [0] [+]) {−𝐒ₙ(ℕ.𝟎)}    = [−] ([0])
[ℤ]-simple-induction {P} ([ℤ]-simple-ind [−] [0] [+]) {−𝐒ₙ(ℕ.𝐒(n))} = [−] ([ℤ]-simple-induction {P} ([ℤ]-simple-ind [−] [0] [+]) {−𝐒ₙ(n)})

-- An intuitive induction proof method on integers
record [ℤ]-induction-data (P : ℤ → Stmt) : Set(ℓ) where
  constructor [ℤ]-ind
  field
    [−] : ∀{n} → P(n) → P(𝐏(n))
    [0] : ∃(n ↦ P(n))
    [+] : ∀{n} → P(n) → P(𝐒(n))

{-
[ℤ]-induction : ∀{P} → [ℤ]-induction-data(P) → (∀{n} → P(n))
[ℤ]-induction {_} ([ℤ]-ind [−] [0] [+]) {𝟎} with [0]
... | [∃]-intro (𝟎)     ⦃ base ⦄ = base
... | [∃]-intro (+𝐒ₙ(n)) ⦃ base ⦄ = [ℤ]-induction record{[0] = [∃]-intro (+ₙ n) ([−] {+𝐒ₙ(n)} (base)) ; [+] = [+] ; [−] = [−]} {𝟎}
... | [∃]-intro (−𝐒ₙ(n)) ⦃ base ⦄ = [ℤ]-induction record{[0] = [∃]-intro (−ₙ n) ([+] {−𝐒ₙ(n)} (base)) ; [+] = [+] ; [−] = [−]} {𝟎}
[ℤ]-induction {P} ([ℤ]-ind [−] [0] [+]) {+𝐒ₙ(n)} = [+]  ([ℤ]-induction {P} ([ℤ]-ind [−] [0] [+]) {+ n})
[ℤ]-induction {P} ([ℤ]-ind [−] [0] [+]) {−𝐒ₙ(n)} = [−]' ([ℤ]-induction {P} ([ℤ]-ind [−] [0] [+]) {+ n}) where
  [−]' : ∀{n} → P(− n) → P(𝐏(− n))
  [−]' = [≡]-elimᵣ [𝐏][−𝐒ₙ]-identity [−]
-}



[𝐒][−𝐒]-is-negative : ∀{x} → 𝐒(−𝐒ₙ x) ≡ −ₙ x
[𝐒][−𝐒]-is-negative{ℕ.𝟎}    = [≡]-intro
[𝐒][−𝐒]-is-negative{ℕ.𝐒(_)} = [≡]-intro
{-# REWRITE [𝐒][−𝐒]-is-negative #-}



[−ₙ]-identityᵣ : ∀{x} → (x −ₙ ℕ.𝟎 ≡ +ₙ x)
[−ₙ]-identityᵣ = [≡]-intro

[−ₙ]-almost-identityₗ : ∀{x} → (ℕ.𝟎 −ₙ x ≡ −ₙ x)
[−ₙ]-almost-identityₗ {ℕ.𝟎}    = [≡]-intro
[−ₙ]-almost-identityₗ {ℕ.𝐒(_)} = [≡]-intro
{-# REWRITE [−ₙ]-almost-identityₗ #-}

[−ₙ]-self : ∀{x} → (x −ₙ x ≡ 𝟎)
[−ₙ]-self {ℕ.𝟎}    = [≡]-intro
[−ₙ]-self {ℕ.𝐒(x)} = [−ₙ]-self {x}
{-# REWRITE [−ₙ]-self #-}

[−ₙ][𝐒]-step : ∀{x y} → (ℕ.𝐒(x) −ₙ y ≡ 𝐒(x −ₙ y))
[−ₙ][𝐒]-step {ℕ.𝟎}   {ℕ.𝟎}    = [≡]-intro
[−ₙ][𝐒]-step {ℕ.𝟎}   {ℕ.𝐒(_)} = [≡]-intro
[−ₙ][𝐒]-step {ℕ.𝐒(_)}{ℕ.𝟎}    = [≡]-intro
[−ₙ][𝐒]-step {ℕ.𝐒(x)}{ℕ.𝐒(y)} = [−ₙ][𝐒]-step {x}{y}



[−]-involution : ∀{n} → (−(− n) ≡ n)
[−]-involution {+ₙ ℕ.𝟎}    = [≡]-intro
[−]-involution {+ₙ ℕ.𝐒(x)} = [≡]-intro
[−]-involution {−𝐒ₙ x}     = [≡]-intro
{-# REWRITE [−]-involution #-}

[−]-injectivity : Injective(−_)
[−]-injectivity {a}{b} (−a≡−b) =
  symmetry [−]-involution
  🝖 congruence₁(−_) (−a≡−b)
  🝖 [−]-involution

[−][−ₙ] : ∀{x} → (−(+ₙ x) ≡ −ₙ x)
[−][−ₙ] {ℕ.𝟎}    = [≡]-intro
[−][−ₙ] {ℕ.𝐒(_)} = [≡]-intro
{-# REWRITE [−][−ₙ] #-}

[−]-fixpoint : FixPoint(−_)(𝟎)
[−]-fixpoint = [≡]-intro

{- TODO
[−][+]-preserving : ∀{x y} → (−(x + y) ≡ (− x) + (− y))
[−][+]-preserving {+ₙ ℕ.𝟎   }  {+ₙ ℕ.𝟎   }  = [≡]-intro
[−][+]-preserving {+ₙ ℕ.𝟎   }  {+ₙ ℕ.𝐒(_)}  = [≡]-intro
[−][+]-preserving {+ₙ ℕ.𝐒(_)}  {+ₙ ℕ.𝟎   }  = [≡]-intro
[−][+]-preserving {+ₙ ℕ.𝐒(_)}  {+ₙ ℕ.𝐒(_)}  = [≡]-intro
[−][+]-preserving {+ₙ ℕ.𝟎   }  {−𝐒ₙ ℕ.𝟎   } = [≡]-intro
[−][+]-preserving {+ₙ ℕ.𝟎   }  {−𝐒ₙ ℕ.𝐒(_)} = [≡]-intro
[−][+]-preserving {+ₙ ℕ.𝐒(_)}  {−𝐒ₙ ℕ.𝟎   } = [≡]-intro
[−][+]-preserving {+ₙ ℕ.𝐒(x)}  {−𝐒ₙ ℕ.𝐒(y)} = [−][+]-preserving{+ₙ x}{−𝐒ₙ y}
[−][+]-preserving {−𝐒ₙ ℕ.𝟎   } {+ₙ ℕ.𝟎   }  = [≡]-intro
[−][+]-preserving {−𝐒ₙ ℕ.𝟎   } {+ₙ ℕ.𝐒(_)}  = [≡]-intro
[−][+]-preserving {−𝐒ₙ ℕ.𝐒(_)} {+ₙ ℕ.𝟎   }  = [≡]-intro
[−][+]-preserving {−𝐒ₙ ℕ.𝐒(x)} {+ₙ ℕ.𝐒(y)}  = [−][+]-preserving
[−][+]-preserving {−𝐒ₙ x} {−𝐒ₙ y} = [≡]-intro
-}

{- TODO
[−]-negative-swap : ∀{x y} → (−(x − y) ≡ y − x)
{-# REWRITE [−]-negative-swap #-}
-}



abs-double : ∀{n} → (abs(abs n) ≡ abs(n))
abs-double {+ₙ x}  = [≡]-intro
abs-double {−𝐒ₙ x} = [≡]-intro
{-# REWRITE abs-double #-}

abs-injective-zero : ∀{n} → (abs n ≡ 𝟎) → (n ≡ 𝟎)
abs-injective-zero {𝟎}      ([≡]-intro) = [≡]-intro
abs-injective-zero {+𝐒ₙ(_)} ()
abs-injective-zero {−𝐒ₙ(_)} ()

abs-[−] : ∀{n} → (abs(− n) ≡ abs(n))
abs-[−] {𝟎}       = [≡]-intro
abs-[−] {+𝐒ₙ(_)}  = [≡]-intro
abs-[−] {−𝐒ₙ(_)}  = [≡]-intro
{-# REWRITE abs-[−] #-}

abs-preserving : ∀{x} → (abs(x) ≡ +ₙ(absₙ(x)))
abs-preserving {𝟎}       = [≡]-intro
abs-preserving {+𝐒ₙ(_)}  = [≡]-intro
abs-preserving {−𝐒ₙ(_)}  = [≡]-intro



absₙ-zero : ∀{n} → (absₙ n ≡ ℕ.𝟎) → (n ≡ 𝟎)
absₙ-zero {𝟎}      ([≡]-intro) = [≡]-intro
absₙ-zero {+𝐒ₙ(_)} ()
absₙ-zero {−𝐒ₙ(_)} ()



[+ₙ]-injectivity : Injective(+ₙ_)
[+ₙ]-injectivity([≡]-intro) = [≡]-intro



[−𝐒ₙ]-injectivity : Injective(−𝐒ₙ_)
[−𝐒ₙ]-injectivity([≡]-intro) = [≡]-intro



[+][𝐒]-stepₗ : ∀{x y} → (𝐒(x) + y ≡ 𝐒(x + y))
[+][𝐒]-stepₗ {+ₙ x}       {+ₙ y}       = [≡]-intro
[+][𝐒]-stepₗ {+ₙ ℕ.𝟎   }  {−𝐒ₙ ℕ.𝟎   } = [≡]-intro
[+][𝐒]-stepₗ {+ₙ ℕ.𝟎   }  {−𝐒ₙ ℕ.𝐒(_)} = [≡]-intro
[+][𝐒]-stepₗ {+ₙ ℕ.𝐒(_)}  {−𝐒ₙ ℕ.𝟎   } = [≡]-intro
[+][𝐒]-stepₗ {+ₙ ℕ.𝐒(x)}  {−𝐒ₙ ℕ.𝐒(y)} = [−ₙ][𝐒]-step{x}{ℕ.𝐒(y)}
[+][𝐒]-stepₗ {−𝐒ₙ ℕ.𝟎   } {+ₙ ℕ.𝟎   }  = [≡]-intro
[+][𝐒]-stepₗ {−𝐒ₙ ℕ.𝐒(_)} {+ₙ ℕ.𝟎   }  = [≡]-intro
[+][𝐒]-stepₗ {−𝐒ₙ ℕ.𝟎   } {+ₙ ℕ.𝐒(_)}  = [≡]-intro
[+][𝐒]-stepₗ {−𝐒ₙ ℕ.𝐒(y)} {+ₙ ℕ.𝐒(x)}  = [−ₙ][𝐒]-step{x}{ℕ.𝐒(y)}
[+][𝐒]-stepₗ {−𝐒ₙ ℕ.𝟎   } {−𝐒ₙ ℕ.𝟎   } = [≡]-intro
[+][𝐒]-stepₗ {−𝐒ₙ ℕ.𝐒(_)} {−𝐒ₙ ℕ.𝟎   } = [≡]-intro
[+][𝐒]-stepₗ {−𝐒ₙ ℕ.𝟎   } {−𝐒ₙ ℕ.𝐒(_)} = [≡]-intro
[+][𝐒]-stepₗ {−𝐒ₙ ℕ.𝐒(y)} {−𝐒ₙ ℕ.𝐒(x)} = [≡]-intro

[+]-identityₗ : Identityₗ(_+_)(𝟎)
[+]-identityₗ {+ₙ _}  = [≡]-intro
[+]-identityₗ {−𝐒ₙ _} = [≡]-intro
{-# REWRITE [+]-identityₗ #-}

[+]-identityᵣ : Identityᵣ(_+_)(𝟎)
[+]-identityᵣ {+ₙ _}  = [≡]-intro
[+]-identityᵣ {−𝐒ₙ _} = [≡]-intro
{-# REWRITE [+]-identityᵣ #-}

[+]-identity : Identity(_+_)(𝟎)
[+]-identity = [∧]-intro [+]-identityₗ [+]-identityᵣ

[+]-commutativity : Commutativity(_+_)
[+]-commutativity {+ₙ x}  {+ₙ y}  = congruence₁(+ₙ_) (ℕ.[+]-commutativity {_} {x}{y})
[+]-commutativity {+ₙ _}  {−𝐒ₙ _} = [≡]-intro
[+]-commutativity {−𝐒ₙ _} {+ₙ _}  = [≡]-intro
[+]-commutativity {−𝐒ₙ x} {−𝐒ₙ y} = congruence₁(−𝐒ₙ_ ∘ ℕ.𝐒) (ℕ.[+]-commutativity {_} {x}{y})

[+]-of-negative : ∀{x y} → ((−ₙ x) + (−ₙ y) ≡ −ₙ (x +ₙ y))
[+]-of-negative {ℕ.𝟎}    {ℕ.𝟎}    = [≡]-intro
[+]-of-negative {ℕ.𝟎}    {ℕ.𝐒(_)} = [≡]-intro
[+]-of-negative {ℕ.𝐒(_)} {ℕ.𝟎}    = [≡]-intro
[+]-of-negative {ℕ.𝐒(_)} {ℕ.𝐒(_)} = [≡]-intro
{-# REWRITE [+]-of-negative #-}

[+]-inverseFunctionₗ : InverseFunctionₗ(_+_)(𝟎)(−_)
[+]-inverseFunctionₗ {+ₙ ℕ.𝟎}    = [≡]-intro
[+]-inverseFunctionₗ {+ₙ ℕ.𝐒(_)} = [≡]-intro
[+]-inverseFunctionₗ {−𝐒ₙ _}     = [≡]-intro
{-# REWRITE [+]-inverseFunctionₗ #-}

[+]-inverseFunctionᵣ : InverseFunctionᵣ(_+_)(𝟎)(−_)
[+]-inverseFunctionᵣ {+ₙ ℕ.𝟎}    = [≡]-intro
[+]-inverseFunctionᵣ {+ₙ ℕ.𝐒(_)} = [≡]-intro
[+]-inverseFunctionᵣ {−𝐒ₙ _}     = [≡]-intro
{-# REWRITE [+]-inverseFunctionᵣ #-}

[+][−ₙ]-associativity : ∀{x y z} → ((x +ₙ y) −ₙ z ≡ (+ₙ x) + (y −ₙ z))
[+][−ₙ]-associativity {ℕ.𝟎}   {ℕ.𝟎}   {ℕ.𝟎}    = [≡]-intro
[+][−ₙ]-associativity {ℕ.𝟎}   {ℕ.𝟎}   {ℕ.𝐒(_)} = [≡]-intro
[+][−ₙ]-associativity {ℕ.𝟎}   {ℕ.𝐒(_)}{ℕ.𝟎}    = [≡]-intro
[+][−ₙ]-associativity {ℕ.𝟎}   {ℕ.𝐒(_)}{ℕ.𝐒(_)} = [≡]-intro
[+][−ₙ]-associativity {ℕ.𝐒(_)}{ℕ.𝟎}   {ℕ.𝟎}    = [≡]-intro
[+][−ₙ]-associativity {ℕ.𝐒(_)}{ℕ.𝟎}   {ℕ.𝐒(_)} = [≡]-intro
[+][−ₙ]-associativity {ℕ.𝐒(_)}{ℕ.𝐒(_)}{ℕ.𝟎}    = [≡]-intro
[+][−ₙ]-associativity {ℕ.𝐒(x)}{ℕ.𝐒(y)}{ℕ.𝐒(z)} =
  [−ₙ][𝐒]-step {x +ₙ y}{z}
  🝖 congruence₁(𝐒) ([+][−ₙ]-associativity {x}{ℕ.𝐒(y)}{ℕ.𝐒(z)})
  🝖 symmetry ([+][𝐒]-stepₗ {+ₙ x}{ℕ.𝐒 y −ₙ ℕ.𝐒 z})

{- TODO
[+]-associativity : Associativity(_+_)
[+]-associativity {+ₙ x}       {+ₙ y}       {+ₙ z}       = [≡]-intro
[+]-associativity {+ₙ _}       {+ₙ ℕ.𝟎}     {−𝐒ₙ ℕ.𝟎}    = [≡]-intro
[+]-associativity {+ₙ _}       {+ₙ ℕ.𝐒(_)}  {−𝐒ₙ ℕ.𝟎}    = [≡]-intro
[+]-associativity {+ₙ _}       {+ₙ ℕ.𝟎}     {−𝐒ₙ ℕ.𝐒(_)} = [≡]-intro
[+]-associativity {+ₙ ℕ.𝟎}     {+ₙ ℕ.𝐒(_)}  {−𝐒ₙ ℕ.𝐒(_)} = [≡]-intro
[+]-associativity {+ₙ ℕ.𝐒(x)}  {+ₙ ℕ.𝐒(y)}  {−𝐒ₙ ℕ.𝐒(z)} = [+][−ₙ]-associativity {ℕ.𝐒(x)}{y}{ℕ.𝐒(z)} where -- a where postulate a : ∀{a} → a
-- [+]-associativity {+ₙ _}       {−𝐒ₙ ℕ.𝟎}    {+ₙ _}       = [≡]-intro
-- [+]-associativity {+ₙ _}       {−𝐒ₙ ℕ.𝐒(_)} {+ₙ _}       = [≡]-intro
-- [+]-associativity {+ₙ _}       {−𝐒ₙ x}      {−𝐒ₙ y}      = [≡]-intro
-- [+]-associativity {−𝐒ₙ _}      {+ₙ x}       {+ₙ y}       = [≡]-intro
-- [+]-associativity {−𝐒ₙ _}      {+ₙ _}       {−𝐒ₙ _}      = [≡]-intro
-- [+]-associativity {−𝐒ₙ _}      {−𝐒ₙ _}      {+ₙ _}       = [≡]-intro
[+]-associativity {−𝐒ₙ _}      {−𝐒ₙ x}      {−𝐒ₙ y}      = [≡]-intro
-}

[−]-inverseFunctionₗ : InverseFunctionₗ(_−_)(𝟎)(id)
[−]-inverseFunctionₗ  = [≡]-intro

[−]-inverseFunctionᵣ : InverseFunctionᵣ(_−_)(𝟎)(id)
[−]-inverseFunctionᵣ  = [≡]-intro

[−]-inverseFunction : InverseFunction(_−_)(𝟎)(id)
[−]-inverseFunction = [∧]-intro ([−]-inverseFunctionₗ{𝟎}) ([−]-inverseFunctionᵣ{𝟎}) -- TODO: What? Why is the zeroes okay?
