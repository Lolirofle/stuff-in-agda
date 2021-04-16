module Numeral.Natural.Oper.Modulo.Proofs.Algorithm where

import Lvl
open import Logic
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Oper.Proofs.Order
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Syntax.Function
open import Syntax.Transitivity
open import Type

-- The many steps variant of: `[ r , b ] 𝐒(a') mod' 𝐒(b') = [ 𝐒(r) , b ] a' mod' b'` from the definition.
mod'-ind-step : ∀{r b' a b c} → [ r , b' ] (a + c) mod' (b + c) ≡ [ (r + c) , b' ] a mod' b
mod'-ind-step {_}{_} {_}{_}{𝟎}   = [≡]-intro
mod'-ind-step {r}{b'}{a}{b}{𝐒 c} = mod'-ind-step {𝐒 r}{b'}{a}{b}{c = c}

-- The many steps variant of: `[ r , b ] 𝐒(a') mod' 𝐒(b') = [ 𝐒(r) , b ] a' mod' b'` from the definition when the dividend is greater than the modulus.
mod'-ind-step-modulo : ∀{r m' a m} → [ r , m' ] (a + m) mod' m ≡ [ (r + m) , m' ] a mod' 𝟎
mod'-ind-step-modulo {r}{m'}{a}{𝟎} =
  [ r       , m' ] (a + 𝟎) mod' 𝟎 🝖[ _≡_ ]-[]
  [ (r + 𝟎) , m' ] a       mod' 𝟎 🝖-end
mod'-ind-step-modulo {r}{m'}{a}{𝐒 m} =
  [ r          , m' ] (a + 𝐒(m)) mod' 𝐒(m) 🝖[ _≡_ ]-[]
  [ r          , m' ] 𝐒(a + m)   mod' 𝐒(m) 🝖[ _≡_ ]-[]
  [ 𝐒(r)       , m' ] (a + m)    mod' m    🝖[ _≡_ ]-[ mod'-ind-step-modulo {𝐒 r}{m'}{a}{m} ]
  [ 𝐒(r + m)   , m' ] a          mod' 𝟎    🝖[ _≡_ ]-[]
  [ (r + 𝐒(m)) , m' ] a          mod' 𝟎    🝖-end

-- When states and modulus is zero, the result is zero.
mod'-zero-all-except-dividend : ∀{a} → ([ 0 , 0 ] a mod' 0 ≡ 0)
mod'-zero-all-except-dividend {𝟎}    = [≡]-intro
mod'-zero-all-except-dividend {𝐒(a)} = mod'-zero-all-except-dividend {a}

mod'-greater-dividend : ∀{r b' a b} → (a > b) → ([ r , b' ] a mod' b ≡ [ 𝟎 , b' ] (a −₀ 𝐒(b)) mod' b')
mod'-greater-dividend {r} {b'} {.(𝐒 _)} {𝟎}   (succ ab) = [≡]-intro
mod'-greater-dividend {r} {b'} {.(𝐒 _)} {𝐒 b} (succ ab) = mod'-greater-dividend ab

mod'-zero-modulo-greater-dividend : ∀{r a b} → (a > b) → ([ r , 𝟎 ] a mod' b ≡ 𝟎)
mod'-zero-modulo-greater-dividend {r} {.𝟏}         {𝟎}   (succ {y = 𝟎}   ab) = [≡]-intro
mod'-zero-modulo-greater-dividend {r} {.(𝐒 (𝐒 a))} {𝟎}   (succ {y = 𝐒 a} ab) = mod'-zero-all-except-dividend {a}
mod'-zero-modulo-greater-dividend {r} {.(𝐒 _)}     {𝐒 b} (succ           ab) = mod'-zero-modulo-greater-dividend ab

mod'-lesser-dividend : ∀{r b' a b} → (a ≤ b) → ([ r , b' ] a mod' b ≡ r + a)
mod'-lesser-dividend {r} {b'} min = [≡]-intro
mod'-lesser-dividend {r} {b'} (succ ab) = mod'-lesser-dividend {𝐒 r} {b'} ab

-- When the number is the temporary modulus, the result is zero.
mod'-equal-dividend : ∀{r b' b} → ([ r , b' ] 𝐒(b) mod' b) ≡ 𝟎
mod'-equal-dividend {r}{b'}{b} = mod'-greater-dividend {r}{b'} (reflexivity(_≤_) {𝐒 b})

mod'-sumᵣ-modulo : ∀{r b' a b} → ([ r , b' ] (a + 𝐒(b)) mod' b) ≡ ([ 𝟎 , b' ] a mod' b')
mod'-sumᵣ-modulo {r}{b'}{a}{b} = mod'-greater-dividend {r}{b'}{a + 𝐒(b)}{b} (succ([≤]-of-[+]ᵣ {a}{b})) 🝖 congruence₁(a ↦ [ 𝟎 , b' ] a mod' b') (inverseOperᵣ(_+_)(_−₀_) {a}{b})

-- When the 
mod'-sumₗ-modulo : ∀{r b' a b} → ([ r , b' ] (𝐒(b) + a) mod' b) ≡ ([ 𝟎 , b' ] a mod' b')
mod'-sumₗ-modulo {r}{b'}{a}{b} = congruence₁(a ↦ [ r , b' ] a mod' b) (commutativity(_+_) {𝐒(b)}{a}) 🝖 mod'-sumᵣ-modulo {r}{b'}{a}{b}

mod'-maxᵣ : ∀{r b a b'} → ⦃ _ : (b' ≤ b) ⦄ → (([ r , r + b ] a mod' b') ≤ r + b)
mod'-maxᵣ {r} {b} {𝟎} {b'} ⦃ b'b ⦄ = [≤]-of-[+]ₗ
mod'-maxᵣ {r} {𝟎} {𝐒 a} {.0} ⦃ min ⦄ = mod'-maxᵣ {𝟎} {r} {a} {r} ⦃ reflexivity(_≤_) ⦄
mod'-maxᵣ {r} {𝐒 b} {𝐒 a} {.0} ⦃ min ⦄ = mod'-maxᵣ {𝟎} {𝐒(r + b)} {a} {𝐒(r + b)} ⦃ reflexivity(_≤_) ⦄
mod'-maxᵣ {r} {𝐒 b} {𝐒 a} {𝐒 b'} ⦃ succ {b'} p ⦄ = mod'-maxᵣ {𝐒 r} {b} {a} {b'} ⦃ p ⦄

mod'-maxₗ : ∀{r b a b'} → (([ r , b ] a mod' b') ≤ r + a)
mod'-maxₗ {𝟎}  {_}  {𝟎}  {_}    = min
mod'-maxₗ {𝐒 r}{b}  {𝟎}  {𝐒 b'} = mod'-maxₗ {𝐒 r}{𝟎}{𝟎}{b'}
mod'-maxₗ {𝐒 r}{𝐒 b}{𝟎}  {b'}   = mod'-maxₗ {𝐒 r}{b}{𝟎}{b'}
mod'-maxₗ {𝐒 r}{b}  {𝐒 a}{𝟎}    = mod'-maxₗ {𝟎} {b} {a} {b} 🝖 [≤]-successor ([≤]-successor ([≤]-of-[+]ᵣ {r}))
mod'-maxₗ {r}  {b}  {𝐒 a}{𝐒 b'} = mod'-maxₗ {𝐒 r} {b} {a} {b'}
mod'-maxₗ {𝟎}  {𝟎}  {𝐒 a}{𝟎}    = [≤]-successor(mod'-maxₗ {𝟎} {𝟎} {a} {𝟎})
mod'-maxₗ {𝟎}  {𝐒 b}{𝐒 a}{𝟎}    = [≤]-successor(mod'-maxₗ {0} {𝐒 b} {a} {𝐒 b})
mod'-maxₗ {𝐒 r}{𝟎}  {𝟎}  {𝟎}    = succ(mod'-maxₗ {r}{𝟎}{𝟎}{𝟎})
