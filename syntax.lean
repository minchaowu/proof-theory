/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura

Define propositional calculus, valuation, provability, validity, prove soundness.

This file is based on Floris van Doorn Coq files.
-/
import data.nat data.set 
open nat bool set decidable classical

theorem gnp (S : set ℕ) [finite S] : S ≠ ∅ → ∃₀ n ∈ S, ∀₀ m ∈ S, m ≤ n :=
induction_on_finite S (λ H, absurd rfl H)
(λ a S' finS' notin ih H, 
by_cases
(suppose S' = ∅, 
 have Hl : a ∈ insert a S', from !mem_insert,
 have eq : insert a S' = '{a}, by+ simp,
 have ∀ y, y ∈ insert a S' → y ≤ a, from 
   λ y h, have y ∈ '{a}, by+ simp,
   have y = a, from eq_of_mem_singleton this, by+ simp,
 show _, from exists.intro a (and.intro Hl this))
(assume Hneg, obtain b hb, from ih Hneg, 
 by_cases 
 (suppose a < b, 
  have Hl : b ∈ insert a S', from !subset_insert (and.left hb),
  have ∀ y, y ∈ insert a S' → y ≤ b, from 
    λ y hy, or.elim hy (λ Hl, have y < b, by+ simp, le_of_lt this) 
    (λ Hr, (and.right hb) y Hr),
  show _, from exists.intro b (and.intro Hl this))
 (assume nlt, 
  have le : b ≤ a, from le_of_not_gt nlt,
  have Hl : a ∈ insert a S', from !mem_insert,
  have ∀ y, y ∈ insert a S' → y ≤ a, from 
    λy hy, or.elim hy (λ Hl, le_of_eq Hl) 
    (λ Hr, have y ≤ b, from (and.right hb) y Hr, nat.le_trans this le),
  show _, from exists.intro a (and.intro Hl this))))

theorem ne_empty_of_mem {X : Type} {s : set X} {x : X} (H : x ∈ s) : s ≠ ∅ :=
begin intro Hs, rewrite Hs at H, apply not_mem_empty _ H end

theorem image_of_ne_empty {A B : Type} (f : A → B) (s : set A) (H : s ≠ ∅): f ' s ≠ ∅ :=
obtain a ha, from exists_mem_of_ne_empty H,
have f a ∈ f ' s, from !mem_image_of_mem ha,
show _, from ne_empty_of_mem this

definition PropVar [reducible] := nat

inductive PropF :=
| Var  : PropVar → PropF
| Bot  : PropF
| Conj : PropF → PropF → PropF
| Disj : PropF → PropF → PropF
| Impl : PropF → PropF → PropF

namespace PropF
  notation `#`:max P:max := Var P
  notation A ∨ B         := Disj A B
  notation A ∧ B         := Conj A B
  infixr `⇒`:27          := Impl
  notation `⊥`           := Bot

  definition Neg A       := A ⇒ ⊥
  notation ~ A           := Neg A
  definition Top         := ~⊥
  notation `⊤`           := Top
  definition BiImpl A B  := A ⇒ B ∧ B ⇒ A
  infixr `⇔`:27          := BiImpl

  definition valuation   := PropVar → bool

  definition TrueQ (v : valuation) : PropF → bool
  | TrueQ (# P)   := v P
  | TrueQ ⊥       := ff
  | TrueQ (A ∨ B) := TrueQ A || TrueQ B
  | TrueQ (A ∧ B) := TrueQ A && TrueQ B
  | TrueQ (A ⇒ B) := bnot (TrueQ A) || TrueQ B

  definition is_true [reducible] (b : bool) := b = tt

  -- the valuation v satisfies a list of PropF, if forall (A : PropF) in Γ,
  -- (TrueQ v A) is tt (the Boolean true)
  definition Satisfies v Γ := ∀ A, A ∈ Γ → is_true (TrueQ v A)
  definition Models Γ A    := ∀ v, Satisfies v Γ → is_true (TrueQ v A)

  infix `⊨`:80 := Models

  definition Valid p := ∅ ⊨ p
  reserve infix `⊢`:26

  /- Provability -/

  inductive Nc : set PropF → PropF → Prop :=
  infix ⊢ := Nc
  | Nax   : ∀ Γ A,   A ∈ Γ →             Γ ⊢ A
  | ImpI  : ∀ Γ A B, insert A Γ ⊢ B →          Γ ⊢ A ⇒ B
  | ImpE  : ∀ Γ A B, Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  | BotC  : ∀ Γ A,   insert (~A) Γ ⊢ ⊥ →       Γ ⊢ A
  | AndI  : ∀ Γ A B, Γ ⊢ A → Γ ⊢ B →     Γ ⊢ A ∧ B
  | AndE₁ : ∀ Γ A B, Γ ⊢ A ∧ B →         Γ ⊢ A
  | AndE₂ : ∀ Γ A B, Γ ⊢ A ∧ B →         Γ ⊢ B
  | OrI₁  : ∀ Γ A B, Γ ⊢ A →             Γ ⊢ A ∨ B
  | OrI₂  : ∀ Γ A B, Γ ⊢ B →             Γ ⊢ A ∨ B
  | OrE   : ∀ Γ A B C, Γ ⊢ A ∨ B → insert A Γ ⊢ C → insert B Γ ⊢ C → Γ ⊢ C

  infix ⊢ := Nc

  -- axiom finite_proof : ∀ Γ α, Γ ⊢ α → ∃ s, finite s ∧ s ⊆ Γ ∧ (s ⊢ α)

  definition Provable A := ∅ ⊢ A

  definition Prop_Soundness := ∀ A, Provable A → Valid A

  definition Prop_Completeness := ∀ A, Valid A → Provable A

  lemma subset_insert_of_not_mem {A : Type} {S s: set A} {a : A} (H1 : s ⊆ insert a S) (H2 : a ∉ s) : s ⊆ S :=
  λ x h, or.elim (H1 h)
  (λ Hl, have a ∈ s, by+ simp, absurd this H2) (λ Hr, Hr)

  lemma subset_insert_of_mem {A : Type} {S s: set A} {a : A} (H1 : s ⊆ insert a S) (H2 : a ∈ s) : s \ '{a} ⊆ S :=
  λ x h, have x ∈ insert a S, from H1 (and.left h),
  or.elim this 
  (λ Hl, have x ∈ '{a}, by+ rewrite Hl; apply mem_singleton, absurd this (and.right h)) 
  (λ Hr, Hr)

  lemma subset_diff_of_subset {A : Type} {S s: set A} {a : A} (H1 : s ⊆ insert a S) : s \ '{a} ⊆ S :=
  have s \ '{a} ⊆ s, from diff_subset _ _,
  or.elim (em (a ∈ s)) 
  (λ Hl, subset_insert_of_mem H1 Hl) 
  (λ Hr, subset.trans this (subset_insert_of_not_mem H1 Hr) )

  lemma subset_insert_diff {A : Type} {S: set A} {a : A} : S ⊆ insert a (S \ '{a}) :=
  λ x h, or.elim (em (x = a)) (λ Hl, or.inl Hl) 
  (λ Hr, have x ∉ '{a}, from 
     λ Hneg, have x = a, from eq_of_mem_singleton Hneg, Hr this,
   have x ∈ S \ '{a}, from and.intro h this, or.inr this)

  theorem insert_sub_insert {A : Type} {s₁ s₂ : set A} (a : A) (H : s₁ ⊆ s₂) : insert a s₁ ⊆ insert a s₂ := take x, assume H1, or.elim H1 (λ Hl, or.inl Hl) (λ Hr, or.inr (H Hr))

  open Nc

  lemma weakening : ∀ Γ A, Γ ⊢ A → ∀ Δ, Γ ⊆ Δ → Δ ⊢ A :=
  λ Γ A H, Nc.induction_on H
    (λ Γ A Hin Δ Hs,                   !Nax  (Hs A Hin))
    (λ Γ A B H w Δ Hs,                 !ImpI (w _ (insert_sub_insert A Hs)))
    (λ Γ A B H₁ H₂ w₁ w₂ Δ Hs,          !ImpE (w₁ _ Hs) (w₂ _ Hs))
    (λ Γ A H w Δ Hs,                   !BotC (w _ (insert_sub_insert (~A) Hs)))
    (λ Γ A B H₁ H₂ w₁ w₂ Δ Hs,          !AndI (w₁ _ Hs) (w₂ _ Hs))
    (λ Γ A B H w Δ Hs,                 !AndE₁ (w _ Hs))
    (λ Γ A B H w Δ Hs,                 !AndE₂ (w _ Hs))
    (λ Γ A B H w Δ Hs,                 !OrI₁ (w _ Hs))
    (λ Γ A B H w Δ Hs,                 !OrI₂ (w _ Hs))
    (λ Γ A B C H₁ H₂ H₃ w₁ w₂ w₃ Δ Hs,  !OrE (w₁ _ Hs) (w₂ _ (insert_sub_insert A Hs)) (w₃ _ (insert_sub_insert B Hs)))

  lemma deduction : ∀ Γ A B, Γ ⊢ A ⇒ B → insert A Γ ⊢ B :=
  λ Γ A B H, ImpE _ A _ (!weakening H _ (subset_insert A Γ)) (!Nax (mem_insert A Γ))

  lemma prov_impl : ∀ A B, Provable (A ⇒ B) → ∀ Γ, Γ ⊢ A → Γ ⊢ B :=
  λ A B Hp Γ Ha,
    have wHp : Γ ⊢ (A ⇒ B), from !weakening Hp Γ (empty_subset Γ),
    !ImpE wHp Ha

  lemma Satisfies_cons : ∀ {A Γ v}, Satisfies v Γ → is_true (TrueQ v A) → Satisfies v (insert A Γ) :=
  λ A Γ v s t B BinAG,
    or.elim BinAG
      (λ e : B = A, by rewrite e; exact t)
      (λ i : B ∈ Γ, s _ i)

  theorem Soundness_general : ∀ A Γ, Γ ⊢ A → Γ ⊨ A :=
  λ A Γ H, Nc.induction_on H
    (λ Γ A Hin v s,   (s _ Hin))
    (λ Γ A B H r v s,
      by_cases
        (λ t : is_true (TrueQ v A),
           have aux₁ : Satisfies v (insert A Γ), from Satisfies_cons s t,
           have aux₂ : is_true (TrueQ v B), from r v aux₁,
           bor_inr aux₂)
        (λ f : ¬ is_true (TrueQ v A),
           have aux : bnot (TrueQ v A) = tt, by rewrite (eq_ff_of_ne_tt f),
           bor_inl aux))
    (λ Γ A B H₁ H₂ r₁ r₂ v s,
       have aux₁ : bnot (TrueQ v A) || TrueQ v B = tt, from r₁ v s,
       have aux₂ : TrueQ v A = tt, from r₂ v s,
       by+ rewrite [aux₂ at aux₁, bnot_true at aux₁, ff_bor at aux₁]; exact aux₁)
    (λ Γ A H r v s, by_contradiction
       (λ n : TrueQ v A ≠ tt,
         have aux₁ : TrueQ v A    = ff, from eq_ff_of_ne_tt n,
         have aux₂ : TrueQ v (~A) = tt, begin+ change (bnot (TrueQ v A) || ff = tt), rewrite aux₁ end,
         have aux₃ : Satisfies v (insert (~A) Γ), from Satisfies_cons s aux₂,
         have aux₄ : TrueQ v ⊥ = tt, from r v aux₃,
         absurd aux₄ ff_ne_tt))
    (λ Γ A B H₁ H₂ r₁ r₂ v s,
      have aux₁ : TrueQ v A = tt, from r₁ v s,
      have aux₂ : TrueQ v B = tt, from r₂ v s,
      band_intro aux₁ aux₂)
    (λ Γ A B H r v s,
      have aux : TrueQ v (A ∧ B) = tt, from r v s,
      band_elim_left aux)
    (λ Γ A B H r v s,
      have aux : TrueQ v (A ∧ B) = tt, from r v s,
      band_elim_right aux)
    (λ Γ A B H r v s,
      have aux : TrueQ v A = tt, from r v s,
      bor_inl aux)
    (λ Γ A B H r v s,
      have aux : TrueQ v B = tt, from r v s,
      bor_inr aux)
    (λ Γ A B C H₁ H₂ H₃ r₁ r₂ r₃ v s,
      have aux : TrueQ v A || TrueQ v B = tt, from r₁ v s,
      or.elim (or_of_bor_eq aux)
        (λ At : TrueQ v A = tt,
          have aux : Satisfies v (insert A Γ), from Satisfies_cons s At,
          r₂ v aux)
        (λ Bt : TrueQ v B = tt,
          have aux : Satisfies v (insert B Γ), from Satisfies_cons s Bt,
          r₃ v aux))

  theorem Soundness : Prop_Soundness :=
  λ A, Soundness_general A ∅

-- By Minchao

  theorem finite_proof (Γ : set PropF) (α : PropF) (H : Γ ⊢ α) : ∃ s, finite s ∧ s ⊆ Γ ∧ (s ⊢ α) :=
  Nc.rec_on H
  (λ Γ a Hin,
   have Hl : finite '{a}, from finite_insert _ _,
   have rl : '{a} ⊆ Γ, from λ x h, 
     have x = a, from eq_of_mem_singleton h, by+ simp,
   have rr : '{a} ⊢ a, from !Nax !mem_singleton,
   have finite '{a} ∧ '{a} ⊆ Γ ∧ ('{a} ⊢ a), from and.intro Hl (and.intro rl rr),
   exists.intro '{a} this)
  (λ Γ' a b H ih, 
   obtain s hs, from ih, 
   have prov : s ⊢ b, from and.right (and.right hs),
   have rl : s \ '{a} ⊆ Γ', from subset_diff_of_subset (and.left (and.right hs)),
   have Hl : finite (s \ '{a}), from @finite_diff _ _ _ (and.left hs),
   have s ⊆ insert a (s \ '{a}), from subset_insert_diff,
   have insert a (s \ '{a}) ⊢ b, from !weakening prov _ this,
   have s \ '{a} ⊢ a ⇒ b, from !ImpI this,
   exists.intro (s \ '{a}) (and.intro Hl (and.intro rl this)))
  (λ Γ' a b H ih h1 h2, 
   obtain s₁ h₁, from h1,
   obtain s₂ h₂, from h2,
   have fin : finite (s₁ ∪ s₂), from @finite_union _ _ _ (and.left h₁) (and.left h₂),
   have H1 : (s₁ ∪ s₂) ⊢ a ⇒ b, from !weakening (and.right (and.right h₁)) _ (subset_union_left _ _),
   have (s₁ ∪ s₂) ⊢ a, from !weakening (and.right (and.right h₂)) _ (subset_union_right _ _),
   have rr : (s₁ ∪ s₂) ⊢ b, from !ImpE H1 this,
   have sub : (s₁ ∪ s₂) ⊆ Γ', from union_subset (and.left (and.right h₁)) (and.left (and.right h₂)),
   exists.intro (s₁ ∪ s₂) (and.intro fin (and.intro sub rr)))
  (λ Γ' a H ih, 
   obtain s hs, from ih,
   have prov : s ⊢ ⊥, from and.right (and.right hs),
   have rl : s \ '{~a} ⊆ Γ', from subset_diff_of_subset (and.left (and.right hs)),
   have Hl : finite (s \ '{~a}), from @finite_diff _ _ _ (and.left hs),
   have s ⊆ insert (~a) (s \ '{~a}), from subset_insert_diff,
   have insert (~a) (s \ '{~a}) ⊢ ⊥, from !weakening prov _ this,
   have s \ '{~a} ⊢ a, from !BotC this,
   exists.intro (s \ '{~a}) (and.intro Hl (and.intro rl this)))
  (λ Γ' a b H1 H2 ih1 ih2, 
   obtain s₁ h₁, from ih1,
   obtain s₂ h₂, from ih2,
   have fin : finite (s₁ ∪ s₂), from @finite_union _ _ _ (and.left h₁) (and.left h₂),
   have Ha : (s₁ ∪ s₂) ⊢ a, from !weakening (and.right (and.right h₁)) _ (subset_union_left _ _),
   have Hb : (s₁ ∪ s₂) ⊢ b, from !weakening (and.right (and.right h₂)) _ (subset_union_right _ _),
   have rr : (s₁ ∪ s₂) ⊢ a ∧ b, from !AndI Ha Hb,
   have sub : (s₁ ∪ s₂) ⊆ Γ', from union_subset (and.left (and.right h₁)) (and.left (and.right h₂)),
   exists.intro (s₁ ∪ s₂) (and.intro fin (and.intro sub rr)))
  (λ Γ' a b H ih, 
   obtain s hs, from ih,
   have sub : s ⊆ Γ', from and.left (and.right hs),
   have s ⊢ a, from !AndE₁ (and.right (and.right hs)),
   exists.intro s (and.intro (and.left hs) (and.intro sub this)))
  (λ Γ' a b H ih, 
   obtain s hs, from ih,
   have sub : s ⊆ Γ', from and.left (and.right hs),
   have s ⊢ b, from !AndE₂ (and.right (and.right hs)),
   exists.intro s (and.intro (and.left hs) (and.intro sub this)))
  (λ Γ' a b H ih, 
   obtain s hs, from ih,
   have sub : s ⊆ Γ', from and.left (and.right hs),
   have s ⊢ a ∨ b, from !OrI₁ (and.right (and.right hs)),
   exists.intro s (and.intro (and.left hs) (and.intro sub this)))
  (λ Γ' a b H ih, 
   obtain s hs, from ih,
   have sub : s ⊆ Γ', from and.left (and.right hs),
   have s ⊢ a ∨ b, from !OrI₂ (and.right (and.right hs)),
   exists.intro s (and.intro (and.left hs) (and.intro sub this)))
  (λ Γ' a b c h0 h1 h2 ih1 ih2 ih3, 
   obtain s₁ hs₁, from ih1,
   obtain s₂ hs₂, from ih2,
   obtain s₃ hs₃, from ih3,
   have prov₁ : s₁ ⊢ a ∨ b, from and.right (and.right hs₁),
   have prov₂ : s₂ ⊢ c, from and.right (and.right hs₂),
   have prov₃ : s₃ ⊢ c, from and.right (and.right hs₃),
   have sub₁ : s₁ ⊆ Γ', from and.left (and.right hs₁),
   have fin₁ : finite s₁, from and.left hs₁,
   have ua : s₂ \ '{a} ⊆ Γ', from subset_diff_of_subset (and.left (and.right hs₂)),
   have fina : finite (s₂ \ '{a}), from @finite_diff _ _ _ (and.left hs₂),
   have ub : s₃ \ '{b} ⊆ Γ', from subset_diff_of_subset (and.left (and.right hs₃)),
   have finb : finite (s₃ \ '{b}), from @finite_diff _ _ _ (and.left hs₃),
   have subu : (s₂ \ '{a}) ∪ (s₃ \ '{b}) ⊆ Γ', from union_subset ua ub,
   have sub : s₁ ∪ ((s₂ \ '{a}) ∪ (s₃ \ '{b})) ⊆ Γ', from union_subset sub₁ subu,
   have finu : finite ((s₂ \ '{a}) ∪ (s₃ \ '{b})), from @finite_union _ _ _ fina finb,
   have s₁ ∪ ((s₂ \ '{a}) ∪ (s₃ \ '{b})) ⊆ Γ', from union_subset sub₁ subu,
   have fin : finite (s₁ ∪ ((s₂ \ '{a}) ∪ (s₃ \ '{b}))), from @finite_union _ _ _ fin₁ finu,
   have sub₂ : s₂ ⊆ insert a (s₁ ∪ ((s₂ \ '{a}) ∪ (s₃ \ '{b}))), from 
     λ x h, or.elim (em (x = a)) (λ Hl, or.inl Hl) 
     (λ Hr, have x ∉ '{a}, from λ Hneg, Hr (eq_of_mem_singleton Hneg),
      have x ∈ (s₂ \ '{a}), from and.intro h this, 
      or.inr (or.inr (or.inl this))),
   have sub₃ : s₃ ⊆ insert b (s₁ ∪ ((s₂ \ '{a}) ∪ (s₃ \ '{b}))), from 
     λ x h, or.elim (em (x = b)) (λ Hl, or.inl Hl) 
     (λ Hr, have x ∉ '{b}, from λ Hneg, Hr (eq_of_mem_singleton Hneg),
      have x ∈ (s₃ \ '{b}), from and.intro h this, 
      or.inr (or.inr (or.inr this))),
   have H1 : insert a (s₁ ∪ ((s₂ \ '{a}) ∪ (s₃ \ '{b}))) ⊢ c, from !weakening prov₂ _ sub₂,
   have H2 : insert b (s₁ ∪ ((s₂ \ '{a}) ∪ (s₃ \ '{b}))) ⊢ c, from !weakening prov₃ _ sub₃,
   have s₁ ∪ ((s₂ \ '{a}) ∪ (s₃ \ '{b})) ⊢ a ∨ b, from !weakening prov₁ _ (subset_union_left _ _),
   have rr : s₁ ∪ ((s₂ \ '{a}) ∪ (s₃ \ '{b})) ⊢ c, from !OrE this H1 H2,
   exists.intro (s₁ ∪ ((s₂ \ '{a}) ∪ (s₃ \ '{b}))) (and.intro fin (and.intro sub rr)))

  theorem meta_thm0 {Γ : set PropF} {α : PropF} : Γ ⊢ α ⇒ α := 
  !ImpI (!Nax !mem_insert)

  theorem meta_thm1_left {Γ : set PropF} {α β : PropF} (H : Γ ⊢ ~α) : Γ ⊢ ~(α ∧ β) := 
  have insert (α ∧ β) Γ ⊢ α ∧ β, from !Nax !mem_insert,
  have H1 : insert (α ∧ β) Γ ⊢ α, from !AndE₁ this,
  have insert (α ∧ β) Γ ⊢ ~α, from !weakening H _ (subset_insert _ _),
  show _, from !ImpI (!ImpE this H1)

  theorem meta_thm1_right {Γ : set PropF} {α β : PropF} (H : Γ ⊢ ~β) : Γ ⊢ ~(α ∧ β) := 
  have insert (α ∧ β) Γ ⊢ α ∧ β, from !Nax !mem_insert,
  have H1 : insert (α ∧ β) Γ ⊢ β, from !AndE₂ this,
  have insert (α ∧ β) Γ ⊢ ~β, from !weakening H _ (subset_insert _ _),
  show _, from !ImpI (!ImpE this H1)

  -- should be written using tactics.

  lemma eq_of_shift_insert {A : Type} {S : set A} (a b : A) : insert a (insert b S) = insert b (insert a S) :=
  have H1 : insert a (insert b S) ⊆  insert b (insert a S), from 
    λ x h, or.elim h 
    (λ Hl, or.inr (or.inl Hl)) 
    (λ Hr, or.elim Hr (λ Hlb, or.inl Hlb) (λ Hrb, or.inr (or.inr Hrb))),
  have insert b (insert a S) ⊆  insert a (insert b S), from 
    λ x h, or.elim h 
    (λ Hl, or.inr (or.inl Hl)) 
    (λ Hr, or.elim Hr (λ Hlb, or.inl Hlb) (λ Hrb, or.inr (or.inr Hrb))),
  show _, from eq_of_subset_of_subset H1 this

  theorem meta_thm2 {Γ : set PropF} {α β : PropF} (H1 : Γ ⊢ ~α) (H2 : Γ ⊢ ~β) : Γ ⊢ ~(α ∨ β) := 
  have H3 : insert (α ∨ β) Γ ⊢ α ∨ β, from !Nax !mem_insert,
  have (insert α Γ) ⊢ ⊥, from !deduction H1,
  have insert (α ∨ β) (insert α Γ) ⊢ ⊥, from !weakening this _ (subset_insert _ _),
  have H4 : insert α (insert (α ∨ β) Γ) ⊢ ⊥, by+ rewrite eq_of_shift_insert at this;exact this,
  have (insert β Γ) ⊢ ⊥, from !deduction H2,
  have insert (α ∨ β) (insert β Γ) ⊢ ⊥, from !weakening this _ (subset_insert _ _),
  have insert β (insert (α ∨ β) Γ) ⊢ ⊥, by+ rewrite eq_of_shift_insert at this;exact this,
  have (insert (α ∨ β) Γ) ⊢ ⊥, from !OrE H3 H4 this,
  show _, from !ImpI this

  theorem meta_thm3 {Γ : set PropF} {α β : PropF} (H1 : Γ ⊢ α) (H2 : Γ ⊢ ~β) : Γ ⊢ ~(α ⇒ β) := 
  have H3 : insert (α ⇒ β) Γ ⊢ α ⇒ β, from !Nax !mem_insert,
  have H4 : insert (α ⇒ β) Γ ⊢ ~β, from !weakening H2 _ (subset_insert _ _),
  have insert (α ⇒ β) Γ ⊢ α, from !weakening H1 _ (subset_insert _ _),
  have insert (α ⇒ β) Γ ⊢ β, from !ImpE H3 this,
  have insert (α ⇒ β) Γ ⊢ ⊥, from !ImpE H4 this,
  show _, from !ImpI this

  theorem meta_thm4 {Γ : set PropF} {α β : PropF} (H : Γ ⊢ ~α) : Γ ⊢ α ⇒ β := 
  have insert α Γ ⊢ ⊥, from !deduction H,
  have insert (~β) (insert α Γ) ⊢ ⊥, from !weakening this _ (subset_insert _ _),
  have insert α Γ ⊢ β, from !BotC this,
  show _, from !ImpI this

  theorem meta_thm5 {Γ : set PropF} {α β : PropF} (H : Γ ⊢ β) : Γ ⊢ α ⇒ β := 
  have insert α Γ ⊢ β, from !weakening H _ (subset_insert _ _),
  show _, from !ImpI this

  lemma empty_sat (v : valuation) : Satisfies v ∅ := λ A H, absurd H (!not_mem_empty)

  lemma empty_model (α : PropF) (H : ∅ ⊨ α) : ∀ v, is_true (TrueQ v α) := 
  λ v, H v (empty_sat v)

  lemma invalid_bot : ¬ (∅ ⊨ ⊥) := 
  assume H, 
  let v (a : PropVar) := tt in
  have TrueQ v ⊥ = ff, from rfl,
  have ¬ ff = tt, from bool.no_confusion,
  have ¬ TrueQ v ⊥ = tt, by+ simp,
  have H1 : ∃ v, ¬ is_true (TrueQ v ⊥), from exists.intro v this,
  have ¬ ∃ v, ¬ is_true (TrueQ v ⊥), from not_exists_not_of_forall (empty_model ⊥ H),
  show _, from this H1

  theorem unprov_bot : ¬ (∅ ⊢ ⊥) := λ H, invalid_bot (Soundness ⊥ H)

  definition incon (Γ : set PropF) : Prop := ∃ α, (Γ ⊢ α) ∧ (Γ ⊢ ~ α)

  definition con (Γ : set PropF) : Prop := ¬ incon Γ

  theorem omni {Γ : set PropF} {α : PropF} (H : incon Γ)  : Γ ⊢ α := 
  obtain β Hb, from H,
  have H1 : Γ ⊢ ⊥, from !ImpE (and.right Hb) (and.left Hb),
  have Γ ⊆ insert (~α) Γ, from subset_insert (~α) Γ,
  have insert (~α) Γ ⊢ ⊥, from !weakening H1 (insert (~α) Γ) this,
  show _, from !BotC this

  theorem reverse_omni {Γ : set PropF} (H : ∀ α, Γ ⊢ α)  : incon Γ :=
  exists.intro ⊥ (and.intro (H ⊥) (H (~⊥)))

  theorem incon_of_prov_bot {Γ : set PropF} (H : Γ ⊢ ⊥) : incon Γ :=
  have ∀ α, Γ ⊢ α, from λ α, !BotC (!weakening H _ (subset_insert _ _)),
  show _, from reverse_omni this

  theorem incon_union_of_prov {Γ : set PropF} {α : PropF} (H : Γ ⊢ α) : 
    incon (insert (~α ) Γ) := 
  have Γ ⊆ insert (~α) Γ, from subset_insert (~α) Γ,
  have H1 : insert (~α) Γ ⊢ α, from !weakening H (insert (~α) Γ) this,
  have (~α) ∈ insert (~α) Γ, from !mem_insert,
  have insert (~α) Γ ⊢ ~α, from !Nax this,
  show _, from exists.intro (α) (and.intro H1 this)

  theorem prov_of_incon_union {Γ : set PropF} {α : PropF} (H : incon (insert (~α) Γ)) : Γ ⊢ α := !BotC (omni H)

  definition Satisfiable (Γ : set PropF) := ∃ v, Satisfies v Γ

  -- classical
  theorem TFAE1 {Γ : set PropF} {τ : PropF} (H1 : ∀ {Γ}, con Γ → Satisfiable Γ) (H2 : Γ ⊨ τ) : Γ ⊢ τ :=
  by_contradiction
  (suppose ¬ (Γ ⊢ τ),
   have con (insert (~τ) Γ), from not.mto prov_of_incon_union this,
   have Satisfiable (insert (~τ) Γ), from H1 this,
   obtain v Hv, from this,
   have Satisfies v Γ, from 
     λ x, assume Hx, 
     have Γ ⊆ insert (~τ) Γ, from subset_insert (~τ) Γ,
     have x ∈ insert (~τ) Γ, from this Hx,
     Hv x this,
   have TrueQ v τ = tt, from H2 v this,
   have (~τ) ∈ insert (~τ) Γ, from !mem_insert,
   have TrueQ v (~τ) = tt, from Hv (~τ) this,
   have bnot (TrueQ v τ) || ff = tt, from this,
   have bnot (TrueQ v τ) = tt, by+ simp,
   have TrueQ v τ = ff, from eq_ff_of_bnot_eq_tt this,
   have TrueQ v τ ≠ tt, by+ simp,
   show _, by+ simp)

  theorem TFAE2 {Γ : set PropF} (H1 : ∀ {Γ τ}, Γ ⊨ τ → Γ ⊢ τ) (H2 : con Γ): Satisfiable Γ := 
  by_contradiction
  (suppose ¬ Satisfiable Γ,
   have ∀ v, ¬ Satisfies v Γ, from iff.mp forall_iff_not_exists this,
   have ∀ τ, Γ ⊢ τ, from
     take τ, have Γ ⊨ τ, from λ v, assume Hv, absurd Hv (this v),
     H1 this,
   have incon Γ, from reverse_omni this,
   H2 this)

  definition max_con (Γ : set PropF) := con Γ ∧ ∀ α, α ∉ Γ → incon (insert α Γ)

  noncomputable theory

  definition enum (Γ : set PropF) (n : nat) : set PropF :=
  nat.rec_on n Γ
  (λ pred enum', 
   if con (insert (# pred) enum') then insert (# pred) enum' 
   else insert (~(# pred)) enum')

  lemma con_insert_neg_of_incon {Γ : set PropF} {α : PropF} (H1 : con Γ) (H2 : incon (insert α Γ)) : con (insert (~α) Γ) :=
  assume Hincon,
  have H3 : Γ ⊢ α, from prov_of_incon_union Hincon,
  have Γ ⊢ ~α, from !ImpI (omni H2),
  have Γ ⊢ ⊥, from !ImpE this H3,
  have incon Γ, from incon_of_prov_bot this,
  show _, from H1 this
  
  theorem con_enum {Γ : set PropF} (H : con Γ) (n : nat) : con (enum Γ n) := 
  nat.rec_on n H 
  (λ a ih, by_cases
  (suppose con (insert (# a) (enum Γ a)), 
   have enum Γ (succ a) =  insert (# a) (enum Γ a), from if_pos this,
   show _, by+ simp)
  (assume Hneg,
   have incon : incon (insert (# a) (enum Γ a)), from not_not_elim Hneg,
   have enum Γ (succ a) =  insert (~(# a)) (enum Γ a), from if_neg Hneg,    
   have con (insert (~(# a)) (enum Γ a)), from con_insert_neg_of_incon ih incon,
   show _, by+ simp))

  theorem succ_enum {Γ : set PropF} {n : ℕ} : enum Γ n ⊆ enum Γ (succ n) :=
  nat.rec_on n 
  (by_cases 
   (suppose con (insert (# 0) (enum Γ 0)), 
     have enum Γ (succ 0) = insert (# 0) (enum Γ 0), from if_pos this,
     have enum Γ 0 ⊆ insert (# 0) (enum Γ 0), from subset_insert _ _,
     show _, by+ simp)
   (assume Hneg, 
     have enum Γ (succ 0) = insert (~(# 0)) (enum Γ 0), from if_neg Hneg,
     have enum Γ 0 ⊆ insert (~(# 0)) (enum Γ 0), from subset_insert _ _,
     show _, by+ simp))
  (λ a ih, by_cases
   (suppose con (insert (# (succ a)) (enum Γ (succ a))), 
     have enum Γ (succ (succ a)) = insert (# (succ a)) (enum Γ (succ a)), from if_pos this,
     have enum Γ (succ a) ⊆ insert (# (succ a)) (enum Γ (succ a)), from subset_insert _ _,
     show _, by+ simp)
   (assume Hneg, 
     have enum Γ (succ (succ a)) = insert (~(# (succ a))) (enum Γ (succ a)), from if_neg Hneg,
     have enum Γ (succ a) ⊆ insert (~(# (succ a))) (enum Γ (succ a)), from subset_insert _ _,
     show _, by+ simp))
  
  -- Can be strengthened
  theorem increasing_enum {Γ : set PropF} {n m : ℕ} : n ≤ m → enum Γ n ⊆ enum Γ m :=
  nat.rec_on m 
  (λ H, have n = 0, from eq_zero_of_le_zero H,
   have enum Γ 0 ⊆ enum Γ 0, from subset.refl _,
   show _, by+ simp)
  (λ a ih H, by_cases
    (suppose n = succ a, 
      have enum Γ (succ a) ⊆ enum Γ (succ a), from subset.refl _,
      show _, by+ simp)
    (assume Hneg, 
      have n < succ a, from lt_of_le_of_ne H Hneg,
      have n ≤ a, from le_of_lt_succ this,
      have H1 : enum Γ n ⊆ enum Γ a, from ih this,
      have enum Γ a ⊆ enum Γ (succ a), from succ_enum,
      show _, from subset.trans H1 this))

  section
  parameter Γ : set PropF
  parameter Hcon : con Γ

  definition con_comp_ext : set PropF := {x : PropF | ∃ i, x ∈ enum Γ i}

  private definition index (α : PropF) : ℕ := if cond : α ∈ con_comp_ext then some cond else 0

  -- Maybe we should show further that for any finite set S ⊆ con_com_ext, ∀ s ∈ S, s ∈ enum Γ (max (index ' S)).
  theorem mem_index (α : PropF) (H : α ∈ con_comp_ext) : α ∈ enum Γ (index α) :=
  have index α = some H, from if_pos H,
  have α ∈ enum Γ (some H), from some_spec H,
  show _, by+ simp

  theorem con_con_comp_ext : con con_comp_ext := 
  assume H, obtain s hs, from finite_proof _ ⊥ (!omni H),
  have fins : finite s, from and.left hs,
  let is : set ℕ := index ' s in
  have s ≠ ∅, from λ H, have ∅ ⊢ ⊥, by+ simp, unprov_bot this,
  have nemp : is ≠ ∅, from !image_of_ne_empty this,
  have finite is, from @finite_image _ _ _ _ fins, 
  obtain n hn, from @gnp is this nemp,
  have pb : s ⊢ ⊥, from and.right (and.right hs),
  have ∀ a, a ∈ s → a ∈ enum Γ n, from 
    λ a hin, have index a ∈ is, from mem_image hin rfl,
    have index a ≤ n, from and.right hn (index a) this,
    have sub : enum Γ (index a) ⊆ enum Γ n, from increasing_enum this,
    have a ∈ con_comp_ext, from (and.left (and.right hs)) _ hin,
    have a ∈ enum Γ (index a), from mem_index _ this,
    sub this,
  have enum Γ n ⊢ ⊥, from !weakening pb _ this,
  have incon (enum Γ n), from incon_of_prov_bot this,
  show _, from (con_enum Hcon n) this

  lemma unprov_bot_con_comp : ¬ (con_comp_ext ⊢ ⊥) :=
  assume H, con_con_comp_ext (incon_of_prov_bot H)

  definition max_con_ext : set PropF := {α : PropF | con_comp_ext ⊢ α}

  theorem sub_con_comp_ext : Γ ⊆ con_comp_ext := 
  λ x h, have Γ = enum Γ 0, from rfl, 
  have x ∈ enum Γ 0, by+ rewrite this at h;exact h,
  show _, from exists.intro 0 this

  theorem sub_max_con_ext : Γ ⊆ max_con_ext :=
  λ x h, have x ∈ con_comp_ext, from sub_con_comp_ext h,
  show _, from !Nax this

  -- Induction is not necessary. Can be proved by cases.

  theorem atomic_comp (P : PropVar) : (con_comp_ext ⊢ # P) ∨ (con_comp_ext ⊢ ~(# P)) :=
  nat.rec_on P 
  (or.elim (em (con (insert (# 0) Γ))) 
   (λ Hl, have (# 0) ∈ insert (# 0) Γ, from mem_insert _ _, 
    have enum Γ 1 = insert (# 0) Γ, from if_pos Hl,
    have (# 0) ∈ enum Γ 1, by+ simp,
    have (# 0) ∈ con_comp_ext, from exists.intro 1 this,
    show _, from or.inl (!Nax this)) 
   (λ Hr, have (~(# 0)) ∈ insert (~(# 0)) Γ, from mem_insert _ _, 
    have enum Γ 1 = insert (~(# 0)) Γ, from if_neg Hr,
    have (~(# 0)) ∈ enum Γ 1, by+ simp,
    have (~(# 0)) ∈ con_comp_ext, from exists.intro 1 this,
    show _, from or.inr (!Nax this)))
   (λ a ih, or.elim (em (con (insert (# (succ a)) (enum Γ (succ a)))))
    (λ Hl, have (# (succ a)) ∈ insert (# (succ a)) (enum Γ (succ a)), from mem_insert _ _, 
     have enum Γ (succ (succ a)) = insert (# (succ a)) (enum Γ (succ a)), from if_pos Hl,
     have (# (succ a)) ∈ enum Γ (succ (succ a)), by+ simp,
     have (# (succ a)) ∈ con_comp_ext, from exists.intro (succ (succ a)) this,
     show _, from or.inl (!Nax this) )
    (λ Hr, have (~(# (succ a))) ∈ insert (~(# (succ a))) (enum Γ (succ a)), from mem_insert _ _,
     have enum Γ (succ (succ a)) = insert (~(# (succ a))) (enum Γ (succ a)), from if_neg Hr,
     have (~(# (succ a))) ∈ enum Γ (succ (succ a)), by+ simp,
     have (~(# (succ a))) ∈ con_comp_ext, from exists.intro (succ (succ a)) this,
     show _, from or.inr (!Nax this)))

  theorem comp_con_comp_ext (α : PropF) : (con_comp_ext ⊢ α) ∨ (con_comp_ext ⊢ ~α) :=
  PropF.rec_on α 
  (λ a, atomic_comp a)
  (or.inr (!meta_thm0))
  (λ a b iha ihb, or.elim iha
    (λ Hl, or.elim ihb (λ Hlb, or.inl (!AndI Hl Hlb)) (λ Hrb, or.inr (meta_thm1_right Hrb)))
    (λ Hr, or.inr (meta_thm1_left Hr)))
  (λ a b iha ihb, or.elim iha (λ Hl, or.inl (!OrI₁ Hl)) (λ Hr, or.elim ihb (λ Hlb, or.inl (!OrI₂ Hlb)) (λ Hrb, or.inr (meta_thm2 Hr Hrb))))
 (λ a b iha ihb, or.elim iha (λ Hl, or.elim ihb (λ Hlb, or.inl (meta_thm5 Hlb)) (λ Hrb, or.inr (meta_thm3 Hl Hrb))) (λ Hr, or.inl (meta_thm4 Hr)))

  lemma mutual_exclusion (α : PropF) (H : con_comp_ext ⊢ ~α) : ¬ (con_comp_ext ⊢ α) :=
  assume Hneg, have con_comp_ext ⊢ ⊥, from !ImpE H Hneg,
  have incon con_comp_ext, from incon_of_prov_bot this,
  show _, from con_con_comp_ext this

  lemma mutual_exclusion' (α : PropF) (H : ¬ (con_comp_ext ⊢ α)) : con_comp_ext ⊢ (~α) :=
  or.elim (comp_con_comp_ext α) 
  (λ Hl, absurd Hl H) (λ Hr, Hr)
  
  private definition v (P : PropVar) : bool := if # P ∈ max_con_ext then tt else ff

  theorem ne_ff_of_eq_tt {a : bool} (H : a = tt) : a ≠ ff :=
  by+ rewrite H;apply bool.no_confusion

  theorem ne_tt_of_eq_ff {a : bool} (H : a = ff) : a ≠ tt :=
  by+ rewrite H;apply bool.no_confusion

  theorem sat_v {α : PropF} : α ∈ max_con_ext ↔ is_true (TrueQ v α) := 
  PropF.rec_on α
  (λ a, 
   have Hl : # a ∈ max_con_ext → is_true (TrueQ v (# a)), from
     λ h, have TrueQ v (# a) = v a, from rfl,
     have v a = tt, from if_pos h,
     show _, by+ simp,
   have is_true (TrueQ v (# a)) → # a ∈ max_con_ext, from 
     λ h, by_contradiction
     (assume Hneg, have v a = ff, from if_neg Hneg,
      have v a ≠ tt, from ne_tt_of_eq_ff this,
      this h),
   show _, from iff.intro Hl this)
  (have Hl : ⊥ ∈ max_con_ext → is_true (TrueQ v ⊥), from 
     λ h, absurd h unprov_bot_con_comp,
   have is_true (TrueQ v ⊥) → ⊥ ∈ max_con_ext, from
     λ h, have TrueQ v ⊥ = ff, from rfl,
     have TrueQ v ⊥ ≠ tt, from ne_tt_of_eq_ff this,
     show _, from absurd h this,
    show _, from iff.intro Hl this)
  (λ a b iha ihb, 
   have Hl : (a ∧ b) ∈ max_con_ext → is_true (TrueQ v (a ∧ b)), from
     λ h, 
     have con_comp_ext ⊢ a, from !AndE₁ h,
     have t1 : TrueQ v a = tt, from iff.elim_left iha this,
     have con_comp_ext ⊢ b, from !AndE₂ h,
     have t2 : TrueQ v b = tt, from iff.elim_left ihb this,
     have TrueQ v (a ∧ b) = TrueQ v a && TrueQ v b, from rfl,
     show _, by+ simp,
   have is_true (TrueQ v (a ∧ b)) → (a ∧ b) ∈ max_con_ext, from
     λ h, have TrueQ v (a ∧ b) = TrueQ v a && TrueQ v b, from rfl,
     have eq : tt = TrueQ v a && TrueQ v b, by+ simp,
     have is_true (TrueQ v a), from band_elim_left (eq.symm eq),
     have Ha : a ∈ max_con_ext, from iff.elim_right iha this,
     have is_true (TrueQ v b), from band_elim_right (eq.symm eq),
     have Hb : b ∈ max_con_ext, from iff.elim_right ihb this,
     show _, from !AndI Ha Hb,
   show _, from iff.intro Hl this)
  (λ a b iha ihb, 
   have Hl : (a ∨ b) ∈ max_con_ext → is_true (TrueQ v (a ∨ b)), from
     λ h, or.elim (comp_con_comp_ext a)
     (λ Hl, have TrueQ v a = tt, from iff.elim_left iha Hl,
     have TrueQ v (a ∨ b) = TrueQ v a ||  TrueQ v b, from rfl, 
     show _, by+ simp)
     (λ Hr, or.elim (comp_con_comp_ext b) 
       (λ Hlb, have TrueQ v b = tt, from iff.elim_left ihb Hlb, 
       have TrueQ v (a ∨ b) = TrueQ v a ||  TrueQ v b, from rfl,
       show _, by+ simp) 
       (λ Hrb, have con_comp_ext ⊢ ~(a ∨ b), from meta_thm2 Hr Hrb, 
       have incon con_comp_ext, from incon_of_prov_bot (!ImpE this h),
       show _, from absurd this con_con_comp_ext)),
   have is_true (TrueQ v (a ∨ b)) → (a ∨ b) ∈ max_con_ext, from
     λ h, have TrueQ v a = tt ∨ TrueQ v b = tt, from or_of_bor_eq h,
     or.elim this 
     (λ Hl, have a ∈ max_con_ext, from iff.elim_right iha Hl, !OrI₁ this) 
     (λ Hr, have b ∈ max_con_ext, from iff.elim_right ihb Hr, !OrI₂ this),
    show _, from iff.intro Hl this)
  (λ a b iha ihb, 
    have Hl : (a ⇒ b) ∈ max_con_ext → is_true (TrueQ v (a ⇒ b)), from 
      λ h, or.elim (comp_con_comp_ext a)
      (λ Hl, have b ∈ max_con_ext, from !ImpE h Hl, 
       have TrueQ v b = tt, from iff.elim_left ihb this,
       have TrueQ v (a ⇒ b) = bnot (TrueQ v a) || TrueQ v b, from rfl,
       have TrueQ v (a ⇒ b) = bnot (TrueQ v a) || tt, by+ simp,
       show _, by+ simp)
      (λ Hr, have Hneg : ¬ (con_comp_ext ⊢ a), from !mutual_exclusion Hr, 
       have ¬ (con_comp_ext ⊢ a) ↔ TrueQ v a ≠ tt, from not_iff_not iha,
       have TrueQ v a ≠ tt, from iff.elim_left this Hneg,
       have TrueQ v a = ff, from eq_ff_of_ne_tt this,
       have bnot (TrueQ v a) = tt, by+ simp,
       have TrueQ v (a ⇒ b) = bnot (TrueQ v a) || TrueQ v b, from rfl,
       have TrueQ v (a ⇒ b) = tt || TrueQ v b, by+ simp,  
       show _, by+ simp),
    have is_true (TrueQ v (a ⇒ b)) → (a ⇒ b) ∈ max_con_ext, from 
      λ h, have bnot (TrueQ v a) = tt ∨ TrueQ v b = tt, from or_of_bor_eq h,
      or.elim this
      (λ Hl, have TrueQ v a = ff, from eq_ff_of_bnot_eq_tt Hl, 
       have neq : TrueQ v a ≠ tt, from ne_tt_of_eq_ff this,
       have ¬ (con_comp_ext ⊢ a) ↔ TrueQ v a ≠ tt, from not_iff_not iha,
       have ¬ (con_comp_ext ⊢ a), from iff.elim_right this neq,
       have con_comp_ext ⊢ ~a, from !mutual_exclusion' this,
       show _, from meta_thm4 this)
      (λ Hr, have con_comp_ext ⊢ b, from iff.elim_right ihb Hr,
       show _, from meta_thm5 this),
     show _, from iff.intro Hl this)

  theorem sat_Gamma : Satisfiable Γ:=
  have ∀ α, α ∈ Γ → is_true (TrueQ v α), from 
    λ α h, have α ∈ max_con_ext, from sub_max_con_ext h,
    show _, from iff.elim_left sat_v this,
  show _, from exists.intro v this

  end

  theorem PL_completeness {Γ : set PropF} {τ : PropF} (H : Γ ⊨ τ) : Γ ⊢ τ :=
  show _, from TFAE1 sat_Gamma H

  theorem PL_soundness {Γ : set PropF} {τ : PropF} (H : Γ ⊢ τ) : Γ ⊨ τ :=
  show _, from Soundness_general τ Γ H

  theorem con_of_sat {Γ : set PropF} (H : Satisfiable Γ) : con Γ :=
  obtain v hv, from H,
  have unprov : ¬ (Γ ⊢ ⊥), from 
    assume Hneg, 
    have Γ ⊨ ⊥, from PL_soundness Hneg,
    have eq : is_true (TrueQ v ⊥), from this v hv,
    have TrueQ v ⊥ = ff, from rfl,
    have ¬ TrueQ v ⊥ = tt, from ne_tt_of_eq_ff this,
    show _, from this eq,
  assume Hneg, have Γ ⊢ ⊥, from omni Hneg,
  show _, from unprov this
  
  theorem PL_compactness {Γ : set PropF} (H : ∀ s, finite s → s ⊆ Γ → Satisfiable s) : Satisfiable Γ :=
  have con_fin : ∀ s, finite s → s ⊆ Γ → con s, from 
    λ s fin sub,
    show _, from con_of_sat (H s fin sub),
  have con Γ, from 
    assume Hneg, have Γ ⊢ ⊥, from omni Hneg,
    have ∃ s, finite s ∧ s ⊆ Γ ∧ (s ⊢ ⊥),from !finite_proof this,
    obtain s h, from this,
    have Hcon : con s, from con_fin s (and.left h) (and.left (and.right h)),
    have incon s, from incon_of_prov_bot (and.right (and.right h)),
    show _, from Hcon this,
  show _, from sat_Gamma Γ this

end PropF


