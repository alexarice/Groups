{-# OPTIONS --safe --without-K #-}

open import Algebra.Bundles using (Group)
module Algebra.Group.Machinery {g₁ g₂} (𝓖 : Group g₁ g₂) where

open import Algebra.Group.Symmetric 𝓖
open import Algebra.Group.Symmetric.Equality 𝓖
open import Algebra.Group.Symmetric.PartialEquality 𝓖 renaming (trans to ≣'-trans)

open Group PartSymGroup

applyAt : ∀ f {g} before after → f ≣ g → before ∘ f ∘ after ≣' before ∘ g ∘ after
applyAt f {g} before after p = ∙-congˡ {before} {f ∘ after} {g ∘ after} lem
 where
  lem : f ∘ after ≣' g ∘ after
  lem = ∙-congʳ {after} {f} {g} (weaken p)

applyAtT : ∀ f {g} before after {h}
         → f ≣ g
         → before ∘ g ∘ after ≣' h
         → before ∘ f ∘ after ≣' h
applyAtT f {g} before after p rest = ≣'-trans {before ∘ f ∘ after} {before ∘ g ∘ after} (applyAt f before after p) rest
