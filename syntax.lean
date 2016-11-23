/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura

Define propositional calculus, valuation, provability, validity, prove soundness.

This file is based on Floris van Doorn Coq files.
-/
import data.nat data.set data.list
open nat bool set decidable classical list

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

  definition Provable A := ∅ ⊢ A

  definition Prop_Soundness := ∀ A, Provable A → Valid A

  definition Prop_Completeness := ∀ A, Valid A → Provable A

  open Nc

  theorem insert_sub_insert {A : Type} {s₁ s₂ : set A} (a : A) (H : s₁ ⊆ s₂) : insert a s₁ ⊆ insert a s₂ := take x, assume H1, or.elim H1 (λ Hl, or.inl Hl) (λ Hr, or.inr (H x Hr))

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
     have x ∈ insert (~τ) Γ, from this x Hx,
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

  -- **To prove Lindenbaum's lemma we need countable PropF. How?

  -- definition var (α : PropF) : set PropF := 
  -- PropF.rec_on _ _ _ _ _ _

  -- Below is a constructive version.

  theorem meta_thm0 (Γ : set PropF) (α : PropF) : Γ ⊢ α ⇒ α := 
  !ImpI (!Nax !mem_insert)

  definition vars : PropF → set PropF
  | vars (# P)    := '{# P}
  | vars ⊥       := ∅
  | vars (A ∨ B) := vars A ∪ vars B
  | vars (A ∧ B) := vars A ∪ vars B
  | vars (A ⇒ B) := vars A ∪ vars B

  definition shift_vars : PropF → valuation → set PropF
  | shift_vars (# P) v   := if v P = tt then '{# P} else '{# P ⇒ ⊥}
  | shift_vars ⊥ v      := ∅
  | shift_vars (A ∨ B) v := shift_vars A v ∪ shift_vars B v
  | shift_vars (A ∧ B) v := shift_vars A v ∪ shift_vars B v
  | shift_vars (A ⇒ B) v := shift_vars A v ∪ shift_vars B v

  definition shift_wff (α : PropF) (v : valuation) : PropF := if is_true (TrueQ v α) then α else (~α)

  lemma shift_var_eq (P : PropVar) (v : valuation) : shift_vars (# P) v = insert (shift_wff (# P) v) ∅ := 
  by_cases
  (suppose v P = tt, 
    have shift_vars (# P) v = '{# P}, from if_pos this,
    have TrueQ v (# P) = v P, from rfl,
    have is_true (TrueQ v (# P)), by+ simp,
    have shift_wff (# P) v = # P, from if_pos this,
    show _, by+ simp)
  (suppose v P ≠ tt, 
    have shift_vars (# P) v = '{# P ⇒ ⊥}, from if_neg this,
    have TrueQ v (# P) = v P, from rfl,
    have ¬ is_true (TrueQ v (# P)), by+ simp,
    have shift_wff (# P) v = (# P ⇒ ⊥), from if_neg this,
    show _, by+ simp)

  lemma mem_shift_atom (P : PropVar) (v : valuation) : shift_wff (# P) v ∈ shift_vars (# P) v := by rewrite shift_var_eq; apply mem_insert

  theorem sem_to_syn (α : PropF) (v : valuation) : shift_vars α v ⊢ shift_wff α v :=
  PropF.rec_on α 
  (λ a, !Nax !mem_shift_atom)
  (!meta_thm0)
  (λ α β ihα ihβ, _)
  _
  _


  lemma meta_thm {Γ : set PropF} {α β : PropF} (H1 : insert α Γ ⊢ β) (H2 : insert (~α) Γ ⊢ β) : Γ ⊢ β := sorry

  

  lemma empty_sat (v : valuation) : Satisfies v ∅ := λ A H, absurd H (!not_mem_empty)

  lemma empty_model (α : PropF) (H : ∅ ⊨ α) : ∀ v, is_true (TrueQ v α) := 
  λ v, H v (empty_sat v)

  lemma invalid_atom (P : PropVar) : ¬ (∅ ⊨ # P) := 
  let v (a : PropVar) := if a = P then ff else tt in
  have v P = ff, from if_pos rfl,
  have ¬ ff = tt, from bool.no_confusion,
  have ¬ v P = tt, by+ simp,  
  have H1 : ∃ v, ¬ is_true (TrueQ v (# P)), from exists.intro v this,
  assume H,
  have ¬ ∃ v, ¬ is_true (TrueQ v (# P)), from not_exists_not_of_forall (empty_model (# P) H),
  show _, from this H1
  
  lemma invalid_bot : ¬ (∅ ⊨ ⊥) := 
  assume H, 
  let v (a : PropVar) := tt in
  have TrueQ v ⊥ = ff, from rfl,
  have ¬ ff = tt, from bool.no_confusion,
  have ¬ TrueQ v ⊥ = tt, by+ simp,
  have H1 : ∃ v, ¬ is_true (TrueQ v ⊥), from exists.intro v this,
  have ¬ ∃ v, ¬ is_true (TrueQ v ⊥), from not_exists_not_of_forall (empty_model ⊥ H),
  show _, from this H1

  --lemma 

  -- Simple induction doesn't work
  theorem weak_completeness {α : PropF} : ∅ ⊨ α → ∅ ⊢ α := 
  PropF.rec_on α 
  (λ a H, absurd H (invalid_atom a)) 
  (λ H, absurd H invalid_bot) 
  (λ a b ih1 ih2 H, _) 
_ 
_
  


end PropF
