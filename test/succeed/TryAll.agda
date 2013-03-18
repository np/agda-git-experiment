module TryAll where

open import Common.Reflect
open import Common.Equality

module Test (A B C : Set) (x : A) (y : B) (z : C) where
  -- A0 = tryAll
  A1 = tryAll A
  -- A2 = tryAll A B
  -- A3 = tryAll A B C
  -- A4 = tryAll A (B C)

  a : A
  a = tryAll x y z
  b : B
  b = tryAll x y z
  c : C
  c = tryAll x y z

  a≡x : a ≡ x
  a≡x = refl

  b≡y : b ≡ y
  b≡y = refl

  c≡z : c ≡ z
  c≡z = refl

  -- Currently, trying the first option can solve meta-variables,
  -- therefor having an effect. Here the two next options are
  -- considered ill typed for the goal.
  a2 : _
  a2 = tryAll x y z

  -- this is a manifestation of the previous comment
  test-quoteTerm : quoteTerm (tryAll x y z) ≡ quoteTerm x
  test-quoteTerm = refl

  -- tryAll decision is based only on the given alternatives
  {-
  A≡tryABC : A ≡ tryAll A B C
  A≡tryABC = refl
  -}

open Test
