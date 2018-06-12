module Type {ℓ} where

Type : _
Type = Set(ℓ)

-- Assures that a value has a certain type
typeAscript : (T : Type) → T → T
typeAscript T x = x

syntax typeAscript T x = x :of: T

-- Returns the type of a certain value
typeOf : ∀{T : Type} → T → Type
typeOf {T} _ = T

