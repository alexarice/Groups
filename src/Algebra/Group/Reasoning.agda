{-# OPTIONS --safe --without-K #-}

open import Algebra.Bundles using (Group)
module Algebra.Group.Reasoning {g₁ g₂} (𝓖 : Group g₁ g₂) where

open import Algebra.Group.Symmetric 𝓖
open import Algebra.Group.Symmetric.Equality 𝓖
open Group SymGroup

import Algebra.Reasoning.Magma (magma) as M

open M public hiding (begin_; step-≈; step-≈˘; step-no-focus; step-no-focus˘)

open import Algebra.Group.Reasoning.Reflection 𝓖 public using (begin⟨_⟩_)

open import Algebra.Group.Symmetric.Inclusion 𝓖 public using (⟦⟧;⟦_⟧)
open import Tactic.Homomorphism.Group public hiding (Expr)

open import Data.Tree.Binary.Indexed

open import Data.Product using (_,_)

⌊⌋ : Expr _
⌊⌋ = leaf e , here-l

infixr 2 step-≣ step-≣˘ step-≣-no-focus step-≣-no-focus˘

step-≣ = M.step-≈
step-≣˘ = M.step-≈˘
step-≣-no-focus = M.step-no-focus
step-≣-no-focus˘ = M.step-no-focus˘

syntax step-≣  x rest fx≣g = x ≣⌊  fx≣g ⌋ rest
syntax step-≣˘ x rest g≣fx = x ≣˘⌊ g≣fx ⌋ rest
syntax step-≣-no-focus  g rest g≣h = g ≣⟨  g≣h ⟩ rest
syntax step-≣-no-focus˘ g rest h≣g = g ≣˘⟨ h≣g ⟩ rest
