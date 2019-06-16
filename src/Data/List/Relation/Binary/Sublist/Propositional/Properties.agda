------------------------------------------------------------------------
-- The Agda standard library
--
-- Sublist-related properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Sublist.Propositional.Properties
  {a} {A : Set a} where

open import Data.List using (map)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties
  using (here-injective; there-injective)
open import Data.List.Relation.Binary.Sublist.Propositional
  hiding (map)
import Data.List.Relation.Binary.Sublist.Setoid.Properties
  as SetoidProperties
open import Data.Product using (_,_)
open import Function
open import Level using (Level)
open import Relation.Binary using (Rel; _Respects_; _Respects₂_)
open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Relation.Unary as U using (Pred)

private
  variable
    b p r : Level

------------------------------------------------------------------------
-- Re-exporting most setoid properties as is

private module Setoid = SetoidProperties (P.setoid A)

open Setoid public
  hiding (map⁺; Any-resp-⊆; All-resp-⊇; AllPairs-resp-⊇)

------------------------------------------------------------------------
-- Relationships to other predicates

module _ {P : Pred A p} where

  Any-resp-⊆ : (Any P) Respects _⊆_
  Any-resp-⊆ = Setoid.Any-resp-⊆ (resp P)

  All-resp-⊇ : (All P) Respects _⊇_
  All-resp-⊇ = Setoid.All-resp-⊇ (resp P)

module _ {R : Rel A r} where

  AllPairs-resp-⊇ : (AllPairs R) Respects _⊇_
  AllPairs-resp-⊇ = Setoid.AllPairs-resp-⊇ (resp₂ R)

------------------------------------------------------------------------
-- map

module _ {B : Set b} where

  map⁺ : ∀ {as bs} (f : A → B) → as ⊆ bs → map f as ⊆ map f bs
  map⁺ f = Setoid.map⁺ (setoid B) (cong f)

------------------------------------------------------------------------
-- The `lookup` function induced by a proof that `xs ⊆ ys` is injective

module _ {P : Pred A p} where

  lookup-injective : ∀ {xs ys} {p : xs ⊆ ys} {v w : Any P xs} →
                     lookup p v ≡ lookup p w → v ≡ w
  lookup-injective {p = []}       {}
  lookup-injective {p = _   ∷ʳ _} {v}       {w}       =
    lookup-injective ∘′ there-injective
  lookup-injective {p = x≡y ∷ _}  {here pv} {here pw} =
    cong here ∘′ subst-injective x≡y ∘′ here-injective
  lookup-injective {p = _ ∷ _}    {there v} {there w} =
    cong there ∘′ lookup-injective ∘′ there-injective




------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

All-resp-⊆ = All-resp-⊇
{-# WARNING_ON_USAGE All-resp-⊆
"Warning: All-resp-⊆ was deprecated in v1.2.
Please use All-resp-⊇ instead."
#-}
