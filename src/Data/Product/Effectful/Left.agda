------------------------------------------------------------------------
-- The Agda standard library
--
-- Left-biased universe-sensitive functor and monad instances for the
-- Product type.
--
-- To minimize the universe level of the RawFunctor, we require that
-- elements of B are "lifted" to a copy of B at a higher universe level
-- (a ⊔ b). See the Data.Product.Effectful.Examples for how this is
-- done.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra
open import Level

module Data.Product.Effectful.Left
  {a e} (A : RawMonoid a e) (b : Level) where

open import Data.Product.Base using (_,_; map₁; map₂; zip; uncurry)
import Data.Product.Effectful.Left.Base as Base using (Productₗ; functor)
open import Effect.Applicative using (RawApplicative)
open import Effect.Monad using (RawMonad; RawMonadT; mkRawMonad)
open import Function.Base using (id; flip; _∘_; _∘′_)

open RawMonoid A

------------------------------------------------------------------------
-- Re-export the base contents publically

open Base Carrier b public

------------------------------------------------------------------------
-- Basic records

applicative : RawApplicative Productₗ
applicative = record
  { rawFunctor = functor
  ; pure = ε ,_
  ; _<*>_  = zip _∙_ id
  }

monad : RawMonad Productₗ
monad = record
  { rawApplicative = applicative
  ; _>>=_ = uncurry λ w₁ a f → map₁ (w₁ ∙_) (f a)
  }

-- The monad instance also requires some mucking about with universe levels.
monadT : ∀ {ℓ} → RawMonadT {g₁ = ℓ} (_∘′ Productₗ)
monadT M = record
  { lift = (ε ,_) <$>_
  ; rawMonad = mkRawMonad _
                 (pure ∘′ (ε ,_))
                 (λ ma f → ma >>= uncurry λ a x → map₁ (a ∙_) <$> f x)
  } where open RawMonad M

------------------------------------------------------------------------
-- Get access to other monadic functions

module TraversableA {F} (App : RawApplicative {a ⊔ b} {a ⊔ b} F) where

  open RawApplicative App

  sequenceA : ∀ {A} → Productₗ (F A) → F (Productₗ A)
  sequenceA (x , fa) = (x ,_) <$> fa

  mapA : ∀ {A B} → (A → F B) → Productₗ A → F (Productₗ B)
  mapA f = sequenceA ∘ map₂ f

  forA : ∀ {A B} → Productₗ A → (A → F B) → F (Productₗ B)
  forA = flip mapA

module TraversableM {M} (Mon : RawMonad {a ⊔ b} {a ⊔ b} M) where

  open RawMonad Mon

  open TraversableA rawApplicative public
    renaming
    ( sequenceA to sequenceM
    ; mapA      to mapM
    ; forA      to forM
    )
