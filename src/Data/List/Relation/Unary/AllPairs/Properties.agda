------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to AllPairs
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Unary.AllPairs.Properties where

open import Data.List hiding (any)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.AllPairs as AllPairs
  using (AllPairs; []; _∷_)
import Data.List.Relation.Binary.Sublist.Propositional.Properties as Subset
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (suc-injective)
open import Data.Nat using (zero; suc; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-step)
open import Level using (Level)
open import Function using (_∘_; flip)
open import Relation.Binary using (Rel; DecSetoid)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary using (yes; no)

private
  variable
    a b p ℓ : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Introduction (⁺) and elimination (⁻) rules for list operations
------------------------------------------------------------------------
-- map

module _ {R : Rel A ℓ} {f : B → A} where

  map⁺ : ∀ {xs} → AllPairs (λ x y → R (f x) (f y)) xs →
         AllPairs R (map f xs)
  map⁺ []           = []
  map⁺ (x∉xs ∷ xs!) = All.map⁺ x∉xs ∷ map⁺ xs!

------------------------------------------------------------------------
-- ++

module _ {R : Rel A ℓ} where

  ++⁺ : ∀ {xs ys} → AllPairs R xs → AllPairs R ys →
        All (λ x → All (R x) ys) xs → AllPairs R (xs ++ ys)
  ++⁺ []         Rys _              = Rys
  ++⁺ (px ∷ Rxs) Rys (Rxys ∷ Rxsys) = All.++⁺ px Rxys ∷ ++⁺ Rxs Rys Rxsys

------------------------------------------------------------------------
-- concat

module _ {R : Rel A ℓ} where

  concat⁺ : ∀ {xss} → All (AllPairs R) xss →
            AllPairs (λ xs ys → All (λ x → All (R x) ys) xs) xss →
            AllPairs R (concat xss)
  concat⁺ []           []              = []
  concat⁺ (pxs ∷ pxss) (Rxsxss ∷ Rxss) = ++⁺ pxs (concat⁺ pxss Rxss)
    (All.map All.concat⁺ (All.All-swap Rxsxss))

------------------------------------------------------------------------
-- take and drop

module _ {R : Rel A ℓ} where

  take⁺ : ∀ {xs} n → AllPairs R xs → AllPairs R (take n xs)
  take⁺ {xs} n = Subset.AllPairs-resp-⊇ (Subset.take-⊆ n xs)

  drop⁺ : ∀ {xs} n → AllPairs R xs → AllPairs R (drop n xs)
  drop⁺ {xs} n = Subset.AllPairs-resp-⊇ (Subset.drop-⊆ n xs)

------------------------------------------------------------------------
-- applyUpTo

module _ {R : Rel A ℓ} where

  applyUpTo⁺₁ : ∀ f n → (∀ {i j} → i < j → j < n → R (f i) (f j)) →
                AllPairs R (applyUpTo f n)
  applyUpTo⁺₁ f zero    Rf = []
  applyUpTo⁺₁ f (suc n) Rf =
    All.applyUpTo⁺₁ _ n (Rf (s≤s z≤n) ∘ s≤s) ∷
    applyUpTo⁺₁ _ n (λ i≤j j<n → Rf (s≤s i≤j) (s≤s j<n))

  applyUpTo⁺₂ : ∀ f n → (∀ i j → R (f i) (f j)) → AllPairs R (applyUpTo f n)
  applyUpTo⁺₂ f n Rf = applyUpTo⁺₁ f n (λ _ _ → Rf _ _)

------------------------------------------------------------------------
-- applyDownFrom

module _ {R : Rel A ℓ} where

  applyDownFrom⁺₁ : ∀ f n → (∀ {i j} → j < i → i < n → R (f i) (f j)) →
                    AllPairs R (applyDownFrom f n)
  applyDownFrom⁺₁ f zero    Rf = []
  applyDownFrom⁺₁ f (suc n) Rf =
    All.applyDownFrom⁺₁ _ n (flip Rf ≤-refl)  ∷
    applyDownFrom⁺₁ f n (λ j<i i<n → Rf j<i (≤-step i<n))

  applyDownFrom⁺₂ : ∀ f n → (∀ i j → R (f i) (f j)) → AllPairs R (applyDownFrom f n)
  applyDownFrom⁺₂ f n Rf = applyDownFrom⁺₁ f n (λ _ _ → Rf _ _)

------------------------------------------------------------------------
-- tabulate

module _ {R : Rel A ℓ} where

  tabulate⁺ : ∀ {n} {f : Fin n → A} → (∀ {i j} → i ≢ j → R (f i) (f j)) →
              AllPairs R (tabulate f)
  tabulate⁺ {zero}  fᵢ~fⱼ = []
  tabulate⁺ {suc n} fᵢ~fⱼ =
    All.tabulate⁺ (λ j → fᵢ~fⱼ λ()) ∷
    tabulate⁺ (fᵢ~fⱼ ∘ (_∘ suc-injective))

------------------------------------------------------------------------
-- filter

module _ {R : Rel A ℓ} {P : Pred A p} (P? : Decidable P) where

  filter⁺ : ∀ {xs} → AllPairs R xs → AllPairs R (filter P? xs)
  filter⁺ {xs} = Subset.AllPairs-resp-⊇ (Subset.filter-⊆ P? xs)
