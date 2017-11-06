open import Relation.Binary.Core

module CFG {ℓ} {Type : Set ℓ} where

open import Data.List using (List)
open import Data.List.All
open import Data.List.All.Cumulative renaming (All to All')
open import Data.List.Any
open import Data.List.Many
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Product as P
open import Function
open import Level

module L where
    open import Data.List public

    liftRel : ∀ {a b ℓ} {A : Set a} {B : Set b} → REL A B ℓ → REL (List A) (List B) (a ⊔ b ⊔ ℓ)
    liftRel f xs ys = All (λ x → Any (f x) ys) xs

    liftRel* : ∀ {a b ℓ} {A : Set a} {B : Set b} → REL A B ℓ → REL (List A) (List B) (a ⊔ b ⊔ ℓ)
    liftRel* f xs ys = All (λ x → Many (f x) ys) xs

    unAll : ∀ {a p} {A : Set a} {P : A → Set p} {xs} → All P xs → List (∃ P)
    unAll {xs = []} [] = []
    unAll {xs = x ∷ _} (px ∷ pxs) = (x , px) ∷ unAll pxs

private liftF2 : ∀ {a b c z} {A : Set a} {B : Set b} {C : Set c} {Z : Set z} →
         (A → B → C) → (Z → A) → (Z → B) → (Z → C)
liftF2 _*_ f g z = f z * g z

UntermBlock : ∀ {i} → (List Type → Type → Set i) → Set (ℓ ⊔ i)
UntermBlock Instruction = ∃ λ { (non-φs , φs) → All' (Instruction ∘ (flip L._++_ φs)) non-φs }

module Block {i} {Instruction : List Type → Type → Set i} where
    types : UntermBlock Instruction → List Type
    types ((non-φs , φs) , _) = non-φs L.++ φs

    φTypes : UntermBlock Instruction → List Type
    φTypes ((_ , φs) , _) = φs

record Graph {ℓ' i t} {_≤_ : Rel Type ℓ'}
             (Instruction : List Type → Type → Set i)
             (Terminator  : List Type → ℕ → Set t) : Set (ℓ ⊔ ℓ' ⊔ suc (i ⊔ t)) where
  field untermBlocks : List (UntermBlock Instruction)
        outEdges     : -- Outgoing edges from block, and source for each φ in target block
                       let open Block {Instruction = Instruction}
                           _≥_ = flip _≤_
                       in φTypes ⟨ (liftF2 ∘′ L.liftRel* ∘ L.liftRel) _≥_ on L.map ⟩ types $
                          untermBlocks
        terminators  : -- Terminator for which number of outgoing edges is appropriate
                       All (uncurry Terminator ∘
                            P.map id Data.List.Many.length) (L.unAll outEdges)
