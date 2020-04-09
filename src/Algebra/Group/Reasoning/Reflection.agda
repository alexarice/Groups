{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (Group)

module Algebra.Group.Reasoning.Reflection {g₁ g₂} (𝓖 : Group g₁ g₂) where

open Group 𝓖 hiding (magma)

open import Algebra.Group.Symmetric 𝓖
open import Algebra.Group.Symmetric.Equality 𝓖
open import Algebra.Group.Symmetric.Inclusion 𝓖
open import Algebra.Morphism.Group

open Group SymGroup using (magma)
open import Algebra.Reasoning.Magma magma using (_IsRelatedTo_; relTo)
open import Algebra.Reasoning.Magma.Expr magma using (eval) renaming (Expr to MExpr)

open import Function

open import Tactic.Homomorphism.Group public

open import Data.Bool    as Bool    using (Bool; _∨_; if_then_else_)
open import Data.Maybe   as Maybe   using (Maybe; just; nothing; maybe)
open import Data.List    as List    using (List; _∷_; [])
open import Data.Nat     as ℕ       using (ℕ; suc; zero)
open import Data.Product as Product using (_×_; _,_)

open import Agda.Builtin.Reflection
open import Reflection.TypeChecking.Monad.Syntax
open import Reflection.Argument
open import Reflection.Term using (getName; _⋯⟅∷⟆_)

begin-helper : ∀ {g h} → ⟦ g ⟧ ≣ ⟦ h ⟧ → g ≈ h
begin-helper {g} {h} p = ⟦⟧-injective p

begin-helper2 : ∀ {s} {g : Sym} {h : MExpr s} → g IsRelatedTo h → g ≣ eval h
begin-helper2 (relTo p) = p

constructBackSoln : Term → Term → Term → Term → Term
constructBackSoln f eq lhs rhs =
  let domgrp = quote GroupMorphism.from-group ⟨ def ⟩ f ⟨∷⟩ []
      grp = quote GroupMorphism.to-group ⟨ def ⟩ f ⟨∷⟩ []
      f⇓ = quote f[_⇓]
      f↓ = quote f[_↓]
      l = buildExpr lhs
      r = buildExpr rhs in
  quote begin-helper ⟨ def ⟩ domgrp ⟨∷⟩
  (quote Group.trans ⟨ def ⟩ grp ⟨∷⟩
    (quote Group.trans ⟨ def ⟩ grp ⟨∷⟩
      (quote proof ⟨ def ⟩ f ⟨∷⟩ l ⟨∷⟩ [])
      ⟨∷⟩
      (quote begin-helper2 ⟨ def ⟩ domgrp ⟨∷⟩ eq ⟨∷⟩ [])
      ⟨∷⟩ []
    )
    ⟨∷⟩
    (quote Group.sym ⟨ def ⟩ grp ⟨∷⟩
      (quote proof ⟨ def ⟩ f ⟨∷⟩ r ⟨∷⟩ []) ⟨∷⟩ [])
    ⟨∷⟩
    []) ⟨∷⟩ []


begin-macro : Term → Term → Term → TC _
begin-macro f proof hole = do
  hole' ← inferType hole >>= normalise
  just (lhs , rhs) ← returnTC (getArgs hole')
    where nothing → typeError (termErr hole' ∷ [])
  let soln = constructBackSoln f proof lhs rhs
  unify hole soln

macro
  infix 1 begin⟨_⟩_
  begin⟨_⟩_ : Term → Term → Term → TC _
  begin⟨_⟩_ = begin-macro
