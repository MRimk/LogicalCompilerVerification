import .defs
import .exec
import .comp_def

namespace LoComp

open instr
open aexp
open bexp
open com

def silly_loop {s : state} : com :=
While ( Bc ( s "x" > s "y") )
  (SKIP ;; Assign "x" (num ((s "x") - 1)))


inductive big_step : com × state → state → Prop
| skip {s} :
  big_step (SKIP, s) s
| assign {x a s} :
  big_step (Assign x a, s) (s{x ↦ eval a s})
| seq {S T s t u} (hS : big_step (S, s) t)
    (hT : big_step (T, t) u) :
  big_step (S ;; T, s) u
| ite_true {b : bexp} {S T s t} (hcond : bval b s)
    (hbody : big_step (S, s) t) :
  big_step (com.If b S T, s) t
| ite_false {b : bexp} {S T s t} (hcond : ¬bval b s)
    (hbody : big_step (T, s) t) :
  big_step (com.If b S T, s) t
| while_true {b : bexp} {S s t u} (hcond : bval b s)
    (hbody : big_step (S, s) t)
    (hrest : big_step (While b S, t) u) :
  big_step (While b S, s) u
| while_false {b : bexp} {S s} (hcond : ¬ bval b s) :
  big_step (While b S, s) s

infix ` ⟹ ` : 110 := big_step


/-! ## Properties of the Big-Step Semantics

Equipped with a big-step semantics, we can

* prove properties of the programming language, such as **equivalence proofs**
  between programs and **determinism**;

* reason about **concrete programs**, proving theorems relating final states `t`
  with initial states `s`. -/

lemma big_step_deterministic {S s l r} (hl : (S, s) ⟹ l)
    (hr : (S, s) ⟹ r) :
  l = r :=
begin
  induction' hl,
  case skip {
    cases' hr,
    refl },
  case assign {
    cases' hr,
    refl },
  case seq : S T s t l hS hT ihS ihT {
    cases' hr with _ _ _ _ _ _ _ t' _ hS' hT',
    cases' ihS hS',
    cases' ihT hT',
    refl },
  case ite_true : b S T s t hb hS ih {
    cases' hr,
    { apply ih hr },
    { cc } },
  case ite_false : b S T s t hb hT ih {
    cases' hr,
    { cc },
    { apply ih hr } },
  case while_true : b S s t u hb hS hw ihS ihw {
    cases' hr,
    { cases' ihS hr,
      cases' ihw hr_1,
      refl },
    { cc } },
  { cases' hr,
    { cc },
    { refl } }
end

-- lemma big_step_terminates {S s} :
--   ∃t, (S, s) ⟹ t :=
-- sorry   -- unprovable

lemma big_step_doesnt_terminate {S s t} :
  ¬ (While (Bc ( true)) S, s) ⟹ t :=
begin
  intro hw,
  induction' hw,
  case while_true {
    assumption },
  case while_false {
    simp [bval] at hcond,
    cc }
end

/-! We can define inversion rules about the big-step semantics: -/

@[simp] lemma big_step_skip_iff {s t} :
  (SKIP, s) ⟹ t ↔ t = s :=
begin
  apply iff.intro,
  { intro h,
    cases' h,
    refl },
  { intro h,
    rw h,
    exact big_step.skip }
end

@[simp] lemma big_step_assign_iff {x a s t} :
  (Assign x a, s) ⟹ t ↔ t = s{x ↦ eval a s} :=
begin
  apply iff.intro,
  { intro h,
    cases' h,
    refl },
  { intro h,
    rw h,
    exact big_step.assign }
end

@[simp] lemma big_step_seq_iff {S T s t} :
  (S ;; T, s) ⟹ t ↔ (∃u, (S, s) ⟹ u ∧ (T, u) ⟹ t) :=
begin
  apply iff.intro,
  { intro h,
    cases' h,
    apply exists.intro,
    apply and.intro; assumption },
  { intro h,
    cases' h,
    cases' h,
    apply big_step.seq; assumption }
end

@[simp] lemma big_step_ite_iff {b S T s t} :
  (com.If b S T, s) ⟹ t ↔
  (bval b s ∧ (S, s) ⟹ t) ∨ (¬ bval b s ∧ (T, s) ⟹ t) :=
begin
  apply iff.intro,
  { intro h,
    cases' h,
    { apply or.intro_left,
      cc },
    { apply or.intro_right,
      cc } },
  { intro h,
    cases' h; cases' h,
    { apply big_step.ite_true; assumption },
    { apply big_step.ite_false; assumption } }
end

lemma big_step_while_iff {b S s u} :
  (While b S, s) ⟹ u ↔
  (∃t, bval b s ∧ (S, s) ⟹ t ∧ (While b S, t) ⟹ u)
  ∨ (¬ bval b s ∧ u = s) :=
begin
  apply iff.intro,
  { intro h,
    cases' h,
    { apply or.intro_left,
      apply exists.intro t,
      cc },
    { apply or.intro_right,
      cc } },
  { intro h,
    cases' h,
    case inl {
      cases' h with t h,
      cases' h with hb h,
      cases' h with hS hwhile,
      exact big_step.while_true hb hS hwhile },
    case inr {
      cases' h with hb hus,
      rw hus,
      exact big_step.while_false hb } }
end

lemma big_step_while_true_iff {b : bexp} {S s u}
    (hcond : bval b s) :
  (While b S, s) ⟹ u ↔
  (∃t, (S, s) ⟹ t ∧ (While b S, t) ⟹ u) :=
by rw big_step_while_iff; simp [hcond]

@[simp] lemma big_step_while_false_iff {b : bexp}
    {S s t} (hcond : ¬ bval b s) :
  (While b S, s) ⟹ t ↔ t = s :=
by rw big_step_while_iff; simp [hcond]



end LoComp