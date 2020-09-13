module Numeral.Natural.Function.GreatestCommonDivisor.Proofs where

-- postulate gcd-identityₗ : ∀{b} → (gcd(𝟎)(b) ≡ b)
-- gcd-identityₗ {𝟎}    = [≡]-intro
-- gcd-identityₗ {𝐒(b)} = gcd-identityₗ {b}
  -- gcd(𝟎)(𝐒(b))
  -- = gcd(𝐒(b))(_mod_ 𝟎 (𝐒(b)) ⦃ [𝐒]-not-0 ⦄)
  -- = gcd(𝐒(b))(𝟎)

-- gcd-identityᵣ : ∀{a} → (gcd(a)(𝟎) ≡ a)
-- gcd-identityᵣ = [≡]-intro

-- postulate gcd-annihilatorₗ : ∀{b} → (gcd(1)(b) ≡ 1)

-- postulate gcd-annihilatorᵣ : ∀{a} → (gcd(a)(1) ≡ 1)

-- postulate gcd-of-mod : ∀{a b} → (gcd(𝐒(b))(a) ≡ gcd(𝐒(b))(_mod_ a (𝐒(b)) ⦃ [𝐒]-not-0 ⦄))

-- postulate gcd-commutativity : Commutativity(gcd)
-- gcd-commutativity {𝟎}   {𝟎}    = [≡]-intro
-- gcd-commutativity {𝟎}   {𝐒(b)} = [≡]-intro
-- gcd-commutativity {𝐒(a)}{𝟎}    = [≡]-intro
-- gcd-commutativity {𝐒(a)}{𝐒(b)} = [≡]-intro

-- postulate gcd-associativity : Associativity(gcd)

-- postulate gcd-same : ∀{a} → (gcd(a)(a) ≡ a)

-- postulate gcd-dividesₗ : ∀{a b} → (gcd(a)(b) ∣ a)
-- gcd-dividesₗ {a}{b} = 

-- postulate gcd-dividesᵣ : ∀{a b} → (gcd(a)(b) ∣ b)

-- postulate gcd-min : ∀{a b} → (gcd(a)(b) ≤ min(a)(b))

-- postulate gcd-with-[+] : ∀{a b} → (gcd(a + b)(b) ≡ gcd(a)(b))

-- postulate gcd-with-[⋅] : ∀{a b} → (gcd(a ⋅ b)(b) ≡ b)

-- postulate gcd-coprime : ∀{a b} → CoPrime(a / gcd(a)(b))(b / gcd(a)(b))

-- postulate gcd-divisors : ∀{a b d} → (d ∣ a) → (d ∣ b) → (d ∣ gcd(a)(b))
