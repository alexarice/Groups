{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (Group)

module Algebra.Group.Symmetric.Base {g₁ g₂} (𝓖 : Group g₁ g₂) where

open Group 𝓖

open import Function.Inverse renaming (sym to inv')

Sym : Set _
Sym = Inverse setoid setoid

e : Sym
e = id

inv : Sym → Sym
inv = inv'
