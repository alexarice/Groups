{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (Group)

module Algebra.Group.Symmetric {g₁ g₂} (𝓖 : Group g₁ g₂) where

open Group 𝓖

open import Algebra using (Op₂; Op₁)
open import Function.Inverse renaming (sym to inv'; _∘_ to _∘'_)

Sym : Set _
Sym = Inverse setoid setoid

e : Sym
e = id

inv : Op₁ Sym
inv = inv'

infixl 60 _∘_
_∘_ : Op₂ Sym
_∘_ = _∘'_
