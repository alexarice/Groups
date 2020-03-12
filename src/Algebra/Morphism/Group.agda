{-# OPTIONS --without-K --safe #-}

module Algebra.Morphism.Group where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism
open import Level

record GroupMorphism {c₁ ℓ₁ c₂ ℓ₂} (From : Group c₁ ℓ₁) (To : Group c₂ ℓ₂) : Set (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
  module F = Group From
  module T = Group To
  field
    morphism : F.Carrier → T.Carrier
    isGroupMorphism : morphism Is From -Group⟶ To
  from-group = From
  to-group = To
  open IsGroupMorphism isGroupMorphism public
