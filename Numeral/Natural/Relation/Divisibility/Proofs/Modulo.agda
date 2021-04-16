module Numeral.Natural.Relation.Divisibility.Proofs.Modulo where

import Lvl
open import Data
open import Functional
open import Logic.Predicate
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.DivMod.Proofs
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Modulo.Proofs
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function.Domain
open import Structure.Operator.Properties
open import Structure.Operator.Proofs.Util
open import Syntax.Transitivity
open import Type

divides-mod : ∀{a b d} → (d ∣ 𝐒(b)) → (d ∣ a) ↔ (d ∣ a mod 𝐒(b))
divides-mod {a}{b}{d} db = [↔]-intro (l db) (r db) where
  l : ∀{a b d} → (d ∣ 𝐒(b)) → (d ∣ a) ← (d ∣ (a mod₀ 𝐒(b)))
  l {a}{b}{𝟎}    db dmod with () ← [0]-only-divides-[0] db
  l {a}{b}{𝐒(d)} db dmod
    with [∃]-intro (𝐒(n)) ⦃ dnb ⦄  ← [↔]-to-[←] divides-[⋅]-existence db
    with [∃]-intro m     ⦃ dmmod ⦄ ← [↔]-to-[←] divides-[⋅]-existence dmod
    = [↔]-to-[→] divides-[⋅]-existence ([∃]-intro (((a ⌊/⌋ (𝐒(d) ⋅ 𝐒(n))) ⋅ 𝐒(n)) + m) ⦃ p ⦄) where
    p : (𝐒(d) ⋅ (((a ⌊/⌋ (𝐒(d) ⋅ 𝐒(n))) ⋅ 𝐒(n)) + m) ≡ a)
    p =
      𝐒(d) ⋅ (((a ⌊/⌋ (𝐒(d) ⋅ 𝐒(n))) ⋅ 𝐒(n)) + m)                     🝖[ _≡_ ]-[ distributivityₗ(_⋅_)(_+_) {𝐒(d)}{(a ⌊/⌋ (𝐒(d) ⋅ 𝐒(n))) ⋅ 𝐒(n)}{m} ]
      (𝐒(d) ⋅ ((a ⌊/⌋ (𝐒(d) ⋅ 𝐒(n))) ⋅ 𝐒(n))) + (𝐒(d) ⋅ m)            🝖[ _≡_ ]-[ [≡]-with(_+ (𝐒(d) ⋅ m)) (One.commuteₗ-assocᵣ {a = 𝐒(d)}{a ⌊/⌋ (𝐒(d) ⋅ 𝐒(n))}{𝐒(n)}) ]
      ((a ⌊/⌋ (𝐒(d) ⋅ 𝐒(n))) ⋅ (𝐒(d) ⋅ 𝐒(n))) + (𝐒(d) ⋅ m)            🝖[ _≡_ ]-[ [≡]-with(((a ⌊/⌋ (𝐒(d) ⋅ 𝐒(n))) ⋅ (𝐒(d) ⋅ 𝐒(n))) +_) dmmod ]
      ((a ⌊/⌋ (𝐒(d) ⋅ 𝐒(n))) ⋅ (𝐒(d) ⋅ 𝐒(n))) + (a mod 𝐒(b))          🝖[ _≡_ ]-[ [≡]-with(expr ↦ ((a ⌊/⌋ (𝐒(d) ⋅ 𝐒(n))) ⋅ (𝐒(d) ⋅ 𝐒(n))) + (a mod 𝐒(expr))) (injective(𝐒) dnb) ]-sym
      ((a ⌊/⌋ (𝐒(d) ⋅ 𝐒(n))) ⋅ (𝐒(d) ⋅ 𝐒(n))) + (a mod (𝐒(d) ⋅ 𝐒(n))) 🝖[ _≡_ ]-[ [⌊/⌋][mod]-is-division-with-remainder {a}{d + 𝐒(d) ⋅ n} ]
      a                                                               🝖-end

  r : ∀{a b d} → (d ∣ 𝐒(b)) → (d ∣ a) → (d ∣ (a mod₀ 𝐒(b)))
  r {a}{b}{𝟎}   db da with [≡]-intro ← [0]-only-divides-[0] da = Div𝟎
  r {a}{b}{𝐒 d} db da
    with [∃]-intro n ⦃ dna ⦄ ← [↔]-to-[←] divides-[⋅]-existence da
    with [∃]-intro m ⦃ dmb ⦄ ← [↔]-to-[←] divides-[⋅]-existence db
    = [↔]-to-[→] divides-[⋅]-existence ([∃]-intro (n mod₀ m) ⦃ p ⦄) where
    p : (𝐒(d) ⋅ (n mod₀ m) ≡ a mod₀ 𝐒(b))
    p =
      𝐒(d) ⋅ (n mod₀ m)          🝖[ _≡_ ]-[ [⋅][mod]-distributivityₗ {n}{m}{𝐒(d)} ]
      (𝐒(d) ⋅ n) mod₀ (𝐒(d) ⋅ m) 🝖[ _≡_ ]-[ [≡]-with(\expr → ((𝐒(d) ⋅ n) mod₀ expr)) dmb ]
      (𝐒(d) ⋅ n) mod₀ 𝐒(b)       🝖[ _≡_ ]-[ [≡]-with(_mod₀ 𝐒(b)) dna ]
      a mod₀ 𝐒(b)                🝖[ _≡_ ]-end
