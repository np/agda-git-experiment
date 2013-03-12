module UnsafeSubst where

open import Common.Prelude using (zero; suc; _+_) renaming (Nat to ℕ)
open import Common.Equality

primitive
  primUnsafeCoerce : ∀ {a b} (A : Set a) (B : Set b) → A → B

unsafeCoerce : ∀ {a b} (A : Set a) (B : Set b) → A → B
unsafeCoerce = primUnsafeCoerce

unsafeSubst : ∀ {a p} {A : Set a} {x y : A} (P : A → Set p) → x ≡ y → P x → P y
unsafeSubst {x = x} {y} P _ = unsafeCoerce (P x) (P y)

module M1 where

  postulate
    A : Set

  δ : A → A
  δ = λ x → unsafeCoerce A (A → A) x x

  Ω : A
  Ω = δ (unsafeCoerce (A → A) A δ)

module M2 where
  postulate
    A   : Set
    x   : A
  unsafeCoerce-computes : unsafeCoerce A A x ≡ x
  unsafeCoerce-computes = refl

module M3 where
  data Vec (A : Set) : ℕ → Set where
    [] : Vec A 0

  _++_ : ∀ {A m n} → Vec A m → Vec A n → Vec A (m + n)
  [] ++ xs = xs

  x+0   : ∀ x → x + 0 ≡ x
  x+0 zero    = refl
  x+0 (suc x) = cong suc (x+0 x)

--lem : ∀ {A n} (xs : Vec A n) → subst (Vec A) (x+0 n) (xs ++ []) ≡ xs
  lem : ∀ {A n} (xs : Vec A n) → unsafeSubst (Vec A) (x+0 n) (xs ++ []) ≡ xs
  lem [] = refl
