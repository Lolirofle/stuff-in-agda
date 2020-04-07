module _ where

open import Function.Iteration using (repeatᵣ ; repeatₗ)

[+]-repeatᵣ-𝐒 : ∀{x y z : ℕ} → (x + y ≡ repeatᵣ y (const 𝐒) z x)
[+]-repeatᵣ-𝐒 {x} {𝟎}       = [≡]-intro
[+]-repeatᵣ-𝐒 {x} {𝐒 y} {z} = [≡]-with(𝐒) ([+]-repeatᵣ-𝐒 {x} {y} {z})

[+]-repeatₗ-𝐒 : ∀{x y z : ℕ} → (x + y ≡ repeatₗ y (const ∘ 𝐒) x z)
[+]-repeatₗ-𝐒 {x} {𝟎}       = [≡]-intro
[+]-repeatₗ-𝐒 {x} {𝐒 y} {z} = [≡]-with(𝐒) ([+]-repeatₗ-𝐒 {x} {y} {z})

[⋅]-repeatᵣ-[+] : ∀{x y} → (x ⋅ y ≡ repeatᵣ y (_+_) x 0)
[⋅]-repeatᵣ-[+] {x} {𝟎}   = [≡]-intro
[⋅]-repeatᵣ-[+] {x} {𝐒 y} = [≡]-with(x +_) ([⋅]-repeatᵣ-[+] {x} {y})

[^]-repeatᵣ-[⋅] : ∀{x y} → (x ^ y ≡ repeatᵣ y (_⋅_) x 1)
[^]-repeatᵣ-[⋅] {x} {𝟎}   = [≡]-intro
[^]-repeatᵣ-[⋅] {x} {𝐒 y} = [≡]-with(x ⋅_) ([^]-repeatᵣ-[⋅] {x} {y})
