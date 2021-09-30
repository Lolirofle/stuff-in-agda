module Numeral.Integer.Construction.Proofs where

import      Lvl
open import Numeral.Integer
open import Numeral.Integer.Construction
open import Numeral.Natural as ℕ using (ℕ)
import      Numeral.Natural.Oper as ℕ
open import Numeral.Natural.Oper.Proofs
open import Relator.Equals

private variable ℓ : Lvl.Level
private variable x y z : ℕ

[−ₙ]-identityᵣ : (x −ₙ ℕ.𝟎 ≡ +ₙ x)
[−ₙ]-identityᵣ = [≡]-intro

[−ₙ]-antiidentityₗ : (ℕ.𝟎 −ₙ x ≡ −ₙ x)
[−ₙ]-antiidentityₗ {ℕ.𝟎}    = [≡]-intro
[−ₙ]-antiidentityₗ {ℕ.𝐒(_)} = [≡]-intro

[−ₙ]-self : (x −ₙ x ≡ 𝟎)
[−ₙ]-self {ℕ.𝟎}    = [≡]-intro
[−ₙ]-self {ℕ.𝐒(x)} = [−ₙ]-self {x}

[−ₙ]-on-[+]ᵣ-redundancy : let _ = x ; _ = y ; _ = z in ((x ℕ.+ z) −ₙ (y ℕ.+ z) ≡ x −ₙ y)
[−ₙ]-on-[+]ᵣ-redundancy{x}{y}{ℕ.𝟎} = [≡]-intro
[−ₙ]-on-[+]ᵣ-redundancy{x}{y}{ℕ.𝐒 z} = [−ₙ]-on-[+]ᵣ-redundancy{x}{y}{z}

[−ₙ]-on-[+]ₗ-redundancy : ((x ℕ.+ y) −ₙ (x ℕ.+ z) ≡ y −ₙ z)
[−ₙ]-on-[+]ₗ-redundancy{ℕ.𝟎}  {y}{z} = [≡]-intro
[−ₙ]-on-[+]ₗ-redundancy{ℕ.𝐒 x}{y}{z} = [−ₙ]-on-[+]ₗ-redundancy{x}{y}{z}
