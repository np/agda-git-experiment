module UnsafeSubst where

open import Common.Prelude using (zero; suc; _+_) renaming (Nat to ℕ)
open import Common.Equality

primitive
  primUnsafeSubst : ∀ {a p} {A : Set a} {x y : A} (P : A → Set p) → x ≡ y → P x → P y


unsafeCoerce : ∀ {a} {A B : Set a} → A ≡ B → A → B
unsafeCoerce = primUnsafeSubst (λ x → x)

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

module M1 where

  postulate
    A : Set
    cool : A ≡ (A → A)

  δ : A → A
  δ = λ x → unsafeCoerce cool x x

  Ω : A
  Ω = δ (unsafeCoerce (sym cool) δ)

module M2 where
  postulate
    A   : Set
    x   : A
    p   : A ≡ A
  foo : unsafeCoerce p x ≡ x
  foo = refl

module M3 where
  data Vec (A : Set) : ℕ → Set where
    [] : Vec A 0

  _++_ : ∀ {A m n} → Vec A m → Vec A n → Vec A (m + n)
  [] ++ xs = xs

  x+0   : ∀ x → x + 0 ≡ x
  x+0 zero    = refl
  x+0 (suc x) = cong suc (x+0 x)

--lem : ∀ {A n} (xs : Vec A n) → subst (Vec A) (x+0 n) (xs ++ []) ≡ xs
  lem : ∀ {A n} (xs : Vec A n) → primUnsafeSubst (Vec A) (x+0 n) (xs ++ []) ≡ xs
  lem [] = refl
