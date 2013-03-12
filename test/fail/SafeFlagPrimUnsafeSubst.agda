module SafeFlagPrimUnsafeSubst where

-- Cannot make an example with the correct type signature for
-- primTrustMe since it requires postulated universe level builtins,
-- which --safe flag will reject.

open import Common.Equality

primitive
  primUnsafeSubst : ∀ {a p} {A : Set a} {x y : A} (P : A → Set p) → x ≡ y → P x → P y
