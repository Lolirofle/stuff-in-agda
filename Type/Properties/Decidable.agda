-- Decidability in the context of types means that it is possible to decide whether a type is empty or have inhabitants.
-- In the case of it having inhabitants, it is possible to extract a witness of the type.
-- Note: When using the types as propositions interpretation of types as a logic system, decidability is equivalent to excluded middle.
module Type.Properties.Decidable where

open import Data
open import Data.Tuple.RaiseTypeᵣ
import      Lvl
import      Lvl.MultiFunctions as Lvl
open import Data.Boolean using (Bool ; 𝑇 ; 𝐹)
open import Function.Multi
open import Logic.Predicate
open import Numeral.Natural
open import Type

private variable ℓ ℓₚ : Lvl.Level
private variable A B C P Q : Type{ℓ}

-- Decider₀(P)(b) states that the boolean value b decides whether the type P is empty or inhabited.
-- When interpreting P as a proposition, the boolean value b decides the truth value of P.
-- Base case of Decider.
data Decider₀ {ℓ} (P : Type{ℓ}) : Bool → Type{Lvl.𝐒(ℓ)} where
  true  : P                  → Decider₀(P)(𝑇)
  false : (P → Empty{Lvl.𝟎}) → Decider₀(P)(𝐹)

-- Elimination rule of Decider₀.
elim : ∀{P} → (Proof : ∀{b} → Decider₀{ℓₚ}(P)(b) → Type{ℓ}) → ((p : P) → Proof(true p)) → ((np : P → Empty) → Proof(false np)) → (∀{b} → (d : Decider₀(P)(b)) → Proof(d))
elim _ fp fnp (true  p)  = fp p
elim _ fp fnp (false np) = fnp np

-- Decider(n)(P)(f) states that the values of the n-ary function f decides whether the values of P is empty or inhabited for a given number of arguments.
-- When interpreting P as an n-ary predicate (proposition), the n-ary function f decides the truth values of P.
Decider : (n : ℕ) → ∀{ℓ}{ℓ𝓈}{As : Types{n}(ℓ𝓈)} → (As ⇉ Type{ℓ}) → (As ⇉ Bool) → Type{Lvl.𝐒(ℓ) Lvl.⊔ Lvl.⨆(ℓ𝓈)}
Decider(0)           = Decider₀
Decider(1)       P f = ∀{x} → Decider₀(P(x))(f(x))
Decider(𝐒(𝐒(n))) P f = ∀{x} → Decider(𝐒(n))(P(x))(f(x))

-- Whether there is a boolean decider for the inhabitedness of a type function.
Decidable : (n : ℕ) → ∀{ℓ}{ℓ𝓈}{As : Types{n}(ℓ𝓈)} → (As ⇉ Type{ℓ}) → Type
Decidable(n)(P) = ∃(Decider(n)(P))

-- The boolean n-ary inhabitedness decider function for a decidable n-ary type function.
decide : (n : ℕ) → ∀{ℓ}{ℓ𝓈}{As : Types{n}(ℓ𝓈)} → (P : As ⇉ Type{ℓ}) → ⦃ dec : Decidable(n)(P) ⦄ → (As ⇉ Bool)
decide(_)(_) ⦃ dec ⦄ = [∃]-witness dec
