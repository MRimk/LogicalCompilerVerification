-- import .love08_operational_semantics_demo .love01_definitions_and_statements_demo
import data.real.basic
import data.vector
import tactic.explode
import tactic.find
import tactic.induction
import tactic.linarith
import tactic.rcases
import tactic.rewrite
import tactic.ring_exp
import tactic.tidy
import tactic.split_ifs


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoComp


def vname := string

def val := ℤ

def stack := list ℤ -- TODO: ???val??? how do we make it accept, because +, -, *, / is not defined for val


namespace rtc

inductive star {α : Sort*} (r : α → α → Prop) (a : α) : α → Prop
| refl {}    : star a
| tail {b c} : star b → r b c → star c

attribute [refl] star.refl

namespace star

variables {α : Sort*} {r : α → α → Prop} {a b c d : α}

@[trans] lemma trans (hab : star r a b) (hbc : star r b c) :
  star r a c :=
begin
  induction' hbc,
  case refl {
    assumption },
  case tail : c d hbc hcd hac {
    exact (tail (hac hab)) hcd }
end

lemma single (hab : r a b) :
  star r a b :=
refl.tail hab

lemma head (hab : r a b) (hbc : star r b c) :
  star r a c :=
begin
  induction' hbc,
  case refl {
    exact (tail refl) hab },
  case tail : c d hbc hcd hac {
    exact (tail (hac hab)) hcd }
end

lemma head_induction_on {α : Sort*} {r : α → α → Prop} {b : α}
  {P : ∀a : α, star r a b → Prop} {a : α} (h : star r a b)
  (refl : P b refl)
  (head : ∀{a c} (h' : r a c) (h : star r c b), P c h → P a (h.head h')) :
  P a h :=
begin
  induction' h,
  case refl {
    exact refl },
  case tail : b c hab hbc ih {
    apply ih,
    show P b _, from
      head hbc _ refl,
    show ∀a a', r a a' → star r a' b → P a' _ → P a _, from
      assume a a' hab hbc, head hab _ }
end

lemma trans_induction_on {α : Sort*} {r : α → α → Prop}
    {p : ∀{a b : α}, star r a b → Prop} {a b : α} (h : star r a b)
    (ih₁ : ∀a, @p a a refl) (ih₂ : ∀{a b} (h : r a b), p (single h))
    (ih₃ : ∀{a b c} (h₁ : star r a b) (h₂ : star r b c), p h₁ →
       p h₂ → p (h₁.trans h₂)) :
  p h :=
begin
  induction' h,
  case refl {
    exact ih₁ a },
  case tail : b c hab hbc ih {
    exact ih₃ hab (single hbc) (ih ih₁ @ih₂ @ih₃) (ih₂ hbc) }
end

lemma lift {β : Sort*} {s : β → β → Prop} (f : α → β)
  (h : ∀a b, r a b → s (f a) (f b)) (hab : star r a b) :
  star s (f a) (f b) :=
hab.trans_induction_on
  (assume a, refl)
  (assume a b, single ∘ h _ _)
  (assume a b c _ _, trans)

lemma mono {p : α → α → Prop} :
  (∀a b, r a b → p a b) → star r a b → star p a b :=
lift id

lemma star_star_eq :
  star (star r) = star r :=
funext
  (assume a,
   funext
     (assume b,
      propext (iff.intro
        (assume h,
         begin
           induction' h,
           { refl },
           { transitivity;
               assumption }
         end)
        (star.mono (assume a b,
           single)))))

end star

end rtc

export rtc


def state : Type := vname → ℤ

def state.update (name : vname) (val : ℤ) (s : state) : state :=
λname', if name' = name then val else s name'

notation s `{` name ` ↦ ` val `}` := state.update name val s

instance : has_emptyc state :=
{ emptyc := λ_, 0 }

@[simp] lemma update_apply (name : vname) (val : ℤ) (s : state) :
  s{name ↦ val} name = val :=
if_pos rfl

@[simp] lemma update_apply_ne (name name' : vname) (val : ℤ) (s : state)
    (h : name' ≠ name) :
  s{name ↦ val} name' = s name' :=
if_neg h

@[simp] lemma update_override (name : vname) (val₁ val₂ : ℤ) (s : state) :
  s{name ↦ val₂}{name ↦ val₁} = s{name ↦ val₁} :=
begin
  apply funext,
  intro name',
  by_cases name' = name;
    simp [h]
end

@[simp] lemma update_swap (name₁ name₂ : vname) (val₁ val₂ : ℤ) (s : state)
    (h : name₁ ≠ name₂) :
  s{name₂ ↦ val₂}{name₁ ↦ val₁} = s{name₁ ↦ val₁}{name₂ ↦ val₂} :=
begin
  apply funext,
  intro name',
  by_cases name' = name₁;
    by_cases name' = name₂;
    simp * at *
end

@[simp] lemma update_id (name : vname) (s : state) :
  s{name ↦ s name} = s :=
begin
  apply funext,
  intro name',
  by_cases name' = name;
    simp * at *
end

@[simp] lemma update_same_const (name : vname) (val : ℤ) :
  (λ_, val){name ↦ val} = (λ_, val) :=
by apply funext; simp




def config := ℤ × state × stack

abbreviation head2 (xs : stack) : ℤ := xs.tail.head
abbreviation tail2 (xs : stack) : stack := xs.tail.tail




inductive instr : Type  -- page 35 
| LOADI : val → instr
| LOAD : vname → instr 
| ADD : instr
| SUB : instr
| MUL : instr
| DIV : instr
| STORE : vname → instr
| JMP : int → instr
| JMPLESS : int → instr
| JMPGE : int → instr
| NOP : instr           -- this is added to avoid option 


open instr



def iexec : instr → config → config
| (LOADI n) (i, s, stk) := (i + 1, s, n :: stk)
| (LOAD v) (i, s, stk) := (i + 1, s, s v :: stk)
| ADD (i, s, stk) := (i + 1, s, (stk.tail.head + stk.head) :: stk.tail.tail)
| SUB (i, s, stk) := (i + 1, s, (stk.tail.head - stk.head) :: stk.tail.tail)
| MUL (i, s, stk) := (i + 1, s, (stk.tail.head * stk.head) :: stk.tail.tail)
| DIV (i, s, stk) := (i + 1, s, (stk.tail.head / stk.head) :: stk.tail.tail)
| (STORE v) (i, s, stk) := (i + 1, s{v ↦ (stk.head)}, stk.tail)
| (JMP n) (i, s, stk) := (i + 1 + n, s, stk)
| (JMPLESS n) (i, s, stk) := 
  if (stk.tail.head) < (stk.head)
  then (i + 1 + n, s, stk.tail.tail)
  else (i + 1, s, stk.tail.tail)
| (JMPGE n) (i, s, stk) := 
  if (stk.tail.head) ≥ (stk.head)
  then (i + 1 + n, s, stk.tail.tail)
  else (i + 1, s, stk.tail.tail)
| NOP (i, s, stk) := (i, s, stk)

/- redefinition for ints rather than nat -/ 
def nth : list instr → ℤ → instr  
| (a :: l) n := if (n = 0) 
  then a
  else nth l (n - 1)
| list.nil n := NOP


/- 
  Execute one instruction
  check if pc is in a valid location in the list 
-/
def exec1  (li : list instr) (c : config)  (c' : config) : Prop := 
( c' = iexec (nth li c.fst) c ∧ 0 ≤ c.fst ∧ c.fst < li.length)  

/-
lemma exec1I [intro, code_pred_intro]:
  "c' = iexec (P!!i) (i,s,stk) ⟹ 0 ≤ i ⟹ i < size P
  ⟹ P ⊢ (i,s,stk) → c'"
by (simp add: exec1_def)

-/

lemma exec1I {li : list instr} {i s stk c'}
  (h1: c' = iexec (nth li i) (i, s, stk))
  (h2 : 0 ≤ i) 
  (h3 : i < li.length):
  exec1 li (i, s, stk) c' := 
  begin 
    simp [exec1],
    simp [h1, h2, h3],
  end






abbreviation exec (li : list instr) (c : config) (c' : config) : Prop :=
star (exec1 li) c c'

/-
lemmas exec_induct = star.induct [of "exec1 P", split_format(complete)]
-/


-- VERIFICATION INFRASTRUCTURE

/-
lemma iexec_shift [simp]: 
  "((n+i',s',stk') = iexec x (n+i,s,stk)) = ((i',s',stk') = iexec x (i,s,stk))"
by(auto split:instr.split)
-/


/-
  if instruction is JMP/JMPLESS/JMPGE then it will have the next 
  instruction pointer which is included in the shift
-/
lemma iexec_shift_with_jmp {n : ℤ}  {i' : ℤ} {i : ℤ} {instr : ℤ}:
n + i' = n + i + 1 + instr ↔ i' = i + 1 + instr :=
begin
  apply iff.intro,
  {
    intro h_no_brackets,
    have h_brackets: n + i' = n + (i + 1 + instr) := 
    begin
      simp [h_no_brackets],
      cc,
    end,
    apply int.add_left_cancel,
    apply h_brackets,
  },
  {
    intro h3,
    simp [h3],
    cc,
  },
end

/-
  if instruction is not JMP/JMPLESS/JMPGE then it will have the next instruction just at + 1
-/
lemma iexec_shift_without_jmp {n : ℤ}  {i' : ℤ} {i : ℤ}:
n + i' = n + i + 1 ↔ i' = i + 1 :=
begin
  apply iff.intro,
  {
    intro h_no_brackets,
    have h_brackets: n + i' = n + (i + 1) := 
    begin
      simp [h_no_brackets],
      cc,
    end,
    apply int.add_left_cancel,
    apply h_brackets,
  },
  {
    intro h3,
    simp [h3],
    cc,
  },
end



lemma iexec_shift {instr n i' s' stk' i s stk}:
((n+i',s',stk') = iexec instr (n+i, s, stk)) = ((i',s',stk') = iexec instr (i,s,stk)) :=
begin
  cases instr,
  case LOADI {
    simp [iexec],
    intros h1 h2,
    apply iexec_shift_without_jmp,
  },
  case LOAD {
    simp [iexec],
    intros h1 h2,
    apply iexec_shift_without_jmp,

  },
  case ADD {
    simp [iexec],
    intros h1 h2,
    apply iexec_shift_without_jmp,

  },
  case SUB {
    simp [iexec],
    intros h1 h2,
    apply iexec_shift_without_jmp,
  },
  case MUL {
    simp [iexec],
    intros h1 h2,
    apply iexec_shift_without_jmp,
  },
  case DIV {
    simp [iexec],
    intros h1 h2,
    apply iexec_shift_without_jmp,
  },
  case STORE {
    simp [iexec],
    intros h1 h2,
    apply iexec_shift_without_jmp,
  },
  case JMP {
    simp [iexec],
    intros h1 h2,
    apply iexec_shift_with_jmp,
  },
  case JMPLESS {
    simp [iexec],
    cases classical.em (head2 stk < list.head stk),
    {
      simp [h],
      intros h1 h2,
      apply iexec_shift_with_jmp,
    },
    {
      simp [h],
      intros h1 h2,
      apply iexec_shift_without_jmp,
    }
  },
  case JMPGE {
    simp [iexec],
    cases classical.em (list.head stk ≤ head2 stk),
    {
      simp [h],
      intros h1 h2,
      apply iexec_shift_with_jmp,
    },
    {
      simp [h],
      intros h1 h2,
      apply iexec_shift_without_jmp,
    },
  },
  case NOP {
    simp [iexec],
  },
end


@[simp]
theorem list.length_nneg {α : Type} (l : list α) : 0 ≤ list.length l :=
begin
  induction l with hd tl hl,
  case list.nil { simp,},
  { simp [list.length_cons, int.coe_nat_succ],}
end


lemma i_pos {i : ℤ} (h_nneg : 0 ≤ i) (h_inotzero : ¬ i = 0) :
0 ≤ i - 1 :=
begin
  cases i,
  {
    cases i,
    {
      simp at h_inotzero,
      cc,
    },
    {
      rw [int.of_nat_succ],
      simp,
    }
    
  },
  {
    simp [h_inotzero],
    simp at h_nneg,
    apply h_nneg,
  }
end


/-
lemma inth_append [simp]:
  "0 ≤ i ⟹
  (xs @ ys) !! i = (if i < size xs then xs !! i else ys !! (i - size xs))"
by (induction xs arbitrary: i) (auto simp: algebra_simps)
-/
lemma nth_append {l1 l2 : list instr} {i : ℤ}
  (h_nneg : 0 ≤ i) :
  nth (l1 ++ l2) i = (
    if i < int.of_nat (list.length l1)
    then nth l1 i
    else nth l2 (i - list.length l1)) :=
  begin
  induction l1 generalizing i,
  case list.nil { 
    simp only [list.nil_append, nth, list.length],
    by_cases (i < int.of_nat 0),
    {
      simp at h,
      apply false.elim, 
      linarith,
    },
    {
      simp at h,
      simp [h],
      have h_neg : ¬ (i < 0) := 
      begin
        linarith,
      end,
      simp [h_neg],
    },
  },
  case list.cons { 
    by_cases h_ite : (i < int.of_nat (list.length (l1_hd :: l1_tl))),
    {
      simp only [h_ite],
      simp,
      by_cases h_izero: (i = 0),
      {
        simp [h_izero],
        simp [nth],
      },
      {
        simp [nth, h_izero],
        rw l1_ih,
        {
          clear l1_ih,
          have h_cond : (i - 1 < int.of_nat (list.length l1_tl)) :=
          begin
            simp only [list.length, int.of_nat_add] at h_ite,
            simp at h_ite,
            simp,
            linarith,
          end,
          simp only [h_cond],
          simp,
        },
        {
          clear l1_ih,
          clear h_ite,
          apply i_pos h_nneg h_izero, 
        },
      }
    },
    {
      simp only [h_ite],
      simp,
      by_cases h_izero : (i = 0),
      {
        simp [list.length] at h_ite,
        apply false.elim,
        linarith,
      },
      {
        have h_ipos : 0 ≤ i - 1, from i_pos h_nneg h_izero,
        specialize l1_ih h_ipos,
        simp [nth] at *,
        simp [h_izero],
        have h_notless : ¬ (i - 1 < list.length l1_tl) := by linarith,
        simp [h_notless] at l1_ih,
        have h_iminusdist : i - (↑(list.length l1_tl) + 1) = i - 1 - ↑(list.length l1_tl) := by ring,
        simp [h_iminusdist],
        apply l1_ih,
      },
    },
  } 
  end




/-
lemma exec1_appendR: "P ⊢ c → c' ⟹ P@P' ⊢ c → c'"
by (auto simp: exec1_def)
-/
lemma exec1_appendR {li c c' li'} (h: exec1 li c c'): 
exec1 (li ++ li') c c' :=
begin
  simp [exec1],
  obtain ⟨h_c', h_zero, h_li⟩ := h,
  induction li,
  case list.nil { 
    unfold_coes, --for int.of_nat in the goal - types
    have h_f : false, begin 
      simp at h_li,
      linarith,
    end,
    cc,    
  },
  case list.cons {
    by_cases h_izero : (c.fst = 0),
    {
      simp,
      simp [nth, h_izero] at *,
      split,
      {apply h_c',},
      linarith,
    },
    {
      have h_inneg : 0 ≤ c.fst, from h_zero,  
      have h_ipos : 0 ≤ c.fst - 1, from i_pos h_zero h_izero, 
      split,
      {
        simp [nth] at h_c',
        simp [h_izero] at h_c',
        simp [nth],
        simp [h_izero],
        have h_append_eq : nth (li_tl ++ li') (c.fst - 1) = nth li_tl (c.fst - 1) :=
        begin 
          rw [nth_append],
          {
            have h_ite : c.fst - 1 < int.of_nat (list.length li_tl) :=
            begin
              have h_less : c.fst < ↑(list.length li_tl) + 1, from h_li,
              simp,
              linarith,
            end,
            simp [h_ite],
            intro h_more,
            simp at h_ite,
            apply false.elim,
            linarith,
          },
          {exact h_ipos,},
        end,
        rw h_c',
        rw h_append_eq,
      },
      split,
      {apply h_inneg,},
      {
        have h_length : c.fst < ↑(list.length (li_hd :: li_tl)), from h_li,
        linarith,
      }
    },
  },
end

/-
lemma exec_appendR: "P ⊢ c →* c' ⟹ P@P' ⊢ c →* c'"
by (induction rule: star.induct) (fastforce intro: star.step exec1_appendR)+

abbreviation exec (li : list instr) (c : config) (c' : config) : Prop :=
star (exec1 li) c c'

inductive star {α : Sort*} (r : α → α → Prop) (a : α) : α → Prop
| refl {}    : star a
| tail {b c} : star b → r b c → star c
-/
lemma exec_appendR {li c c' li'} (h: exec li c c'):
exec (li ++ li') c c' :=
begin
  induction' h,
  case LoComp.rtc.star.refl {
    fconstructor,
  },
  case LoComp.rtc.star.tail {
    apply rtc.star.tail,
    {apply ih,},
    {
      apply exec1_appendR,
      exact h_1,
    },
  },

end

/-
lemma exec1_appendL:
  fixes i i' :: int 
  shows
  "P ⊢ (i,s,stk) → (i',s',stk') ⟹
   P' @ P ⊢ (size(P')+i,s,stk) → (size(P')+i',s',stk')"
  unfolding exec1_def
  by (auto simp del: iexec.simps)
-/

lemma exec1_appendL {i i' :ℤ} {li li' s stk s' stk'}
(h_li : exec1 li (i, s, stk) (i', s', stk')) :
exec1 (li' ++ li) ((list.length li') + i, s, stk) ((list.length li') + i', s', stk') :=
begin
  simp [exec1],
  obtain ⟨ h_c', h_zero, h_length⟩ := h_li,
  simp at *,
  have h_li_i : 0 ≤ ↑(list.length li') + i :=
  begin
    linarith,
  end,
  split,
  {
    simp [iexec_shift, nth_append h_li_i],
    by_cases h_less : (i < 0),
    {
      apply false.elim,
      linarith,
    },
    {
      simp [h_less],
      apply h_c',
    }
  },
  split,
  {
    apply h_li_i,
  },
  {
    apply h_length,
  }
end

/-
lemma exec_appendL:
  fixes i i' :: int 
  shows
 "P ⊢ (i,s,stk) →* (i',s',stk')  ⟹
  P' @ P ⊢ (size(P')+i,s,stk) →* (size(P')+i',s',stk')"
  by (induction rule: exec_induct) (blast intro: star.step exec1_appendL)+
-/
lemma exec_appendL {i i' :ℤ} (li li' i s stk i' s' stk')
(h_single : exec li (i, s, stk) (i', s', stk')) :
exec (li' ++ li) (list.length li' + i, s, stk) (list.length li' + i', s', stk') :=
begin
  induction' h_single,
  case LoComp.rtc.star.refl {
    apply rtc.star.refl,
  },
  case LoComp.rtc.star.tail : b hab hbc ih{
    specialize ih li' b.fst b.snd.fst b.snd.snd,
    simp at ih,
    apply rtc.star.tail,
    {
      apply ih,
    },
    {
      have h_b : b.snd = (b.snd.fst, b.snd.snd) := by finish,
      rw [h_b], 
      apply exec1_appendL,
      simp,
      exact hbc,
    },
  },
end

/-
text‹Now we specialise the above lemmas to enable automatic proofs of
\<^prop>‹P ⊢ c →* c'› where ‹P› is a mixture of concrete instructions and
pieces of code that we already know how they execute (by induction), combined
by ‹@› and ‹#›. Backward jumps are not supported.
The details should be skipped on a first reading.

If we have just executed the first instruction of the program, drop it:›

lemma exec_Cons_1 [intro]:
  "P ⊢ (0,s,stk) →* (j,t,stk') ⟹
  instr#P ⊢ (1,s,stk) →* (1+j,t,stk')"
by (drule exec_appendL[where P'="[instr]"]) simp
-/
lemma exec_cons_1 {s stk j t stk' li instr}
(h : exec li (0, s, stk) (j, t, stk')):
exec (instr :: li) (1, s, stk) (1 + j, t, stk') :=
begin 
  have h_shift : exec ([instr] ++ li) ((list.length [instr]) + 0, s, stk) ((list.length [instr]) + j, t, stk') :=
  begin 
    apply exec_appendL,
    apply j,
    apply j,
    apply h,
  end,
  simp at h_shift,
  exact h_shift,
end
/-
lemma exec_appendL_if[intro]:
  fixes i i' j :: int
  shows
  "size P' <= i
   ⟹ P ⊢ (i - size P',s,stk) →* (j,s',stk')
   ⟹ i' = size P' + j
   ⟹ P' @ P ⊢ (i,s,stk) →* (i',s',stk')"
by (drule exec_appendL[where P'=P']) simp
-/

lemma exec_appendL_if {li' li s stk j s' stk'} {i i' : ℤ}
(h1: int.of_nat (list.length li') <= i )
(h2: exec li (i - list.length li', s, stk) (j, s', stk'))
(h3: i' = list.length li' + j): 
exec (li' ++ li) (i, s, stk) (i', s', stk') :=
begin
  have h_append : exec (li' ++ li) (list.length li' + (i - list.length li'), s, stk) (list.length li' + j, s', stk') :=
  begin
    apply exec_appendL,
    apply i,
    apply i,
    apply h2,
  end,
  simp at h_append,
  rw [h3],
  exact h_append,
end

/-
text‹Split the execution of a compound program up into the execution of its
parts:›

lemma exec_append_trans[intro]:
  fixes i' i'' j'' :: int
  shows
"P ⊢ (0,s,stk) →* (i',s',stk') ⟹
 size P ≤ i' ⟹
 P' ⊢  (i' - size P,s',stk') →* (i'',s'',stk'') ⟹
 j'' = size P + i''
 ⟹
 P @ P' ⊢ (0,s,stk) →* (j'',s'',stk'')"
by(metis star_trans[OF exec_appendR exec_appendL_if])
-/
lemma exec_append_trans {li' li s stk  s' stk' s'' stk''} {i i' j'' i'': ℤ}
(h1: exec li (0, s, stk) (i', s', stk'))
(h2: int.of_nat (list.length li) <= i' )
(h3: exec li' (i' - list.length li, s', stk') (i'', s'', stk''))
(h4: j'' = list.length li + i''): 
exec (li ++ li') (0, s, stk) (j'', s'', stk'') :=
begin
  apply rtc.star.trans,
  have h_appendR_li' : exec (li ++ li') (0, s, stk) (i', s', stk') :=
  begin
    apply exec_appendR h1,
  end, 
  exact h_appendR_li',
  have h_appendL_li : exec (li ++ li') (list.length li + (i' - list.length li), s', stk') (list.length li + i'', s'', stk'') :=
  begin
    apply exec_appendL,
    apply i',
    apply i',
    apply h3,
  end,
  simp at h_appendL_li,
  rw [h4],
  exact h_appendL_li,
end

/-
declare Let_def[simp]


subsection "Compilation"

fun acomp :: "aexp ⇒ instr list" where
"acomp (N n) = [LOADI n]" |
"acomp (V x) = [LOAD x]" |
"acomp (Plus a1 a2) = acomp a1 @ acomp a2 @ [ADD]"

-/
inductive aexp : Type
| num : ℤ → aexp
| var : string → aexp
| add : aexp → aexp → aexp
| sub : aexp → aexp → aexp
| mul : aexp → aexp → aexp
| div : aexp → aexp → aexp

open aexp

def eval  : aexp → state → ℤ
| (num i) s    := i
| (var x) s    := s x
| (add e₁ e₂) s := eval e₁ s + eval e₂ s
| (sub e₁ e₂) s := eval e₁ s - eval e₂ s
| (mul e₁ e₂) s := eval e₁ s * eval e₂ s
| (div e₁ e₂) s := eval e₁ s / eval e₂ s


def acomp : aexp → list instr
| (num n) := [LOADI n]
| (var x) := [LOAD x]
| (add e₁ e₂) := acomp e₁ ++ acomp e₂ ++ [ADD]
| (sub e₁ e₂) := acomp e₁ ++ acomp e₂ ++ [SUB]
| (mul e₁ e₂) := acomp e₁ ++ acomp e₂ ++ [MUL]
| (div e₁ e₂) := acomp e₁ ++ acomp e₂ ++ [DIV]


/-
lemma acomp_correct[intro]:
  "acomp a ⊢ (0,s,stk) →* (size(acomp a),s,aval a s#stk)"
by (induction a arbitrary: stk) fastforce+

-/

lemma acomp_correct {a : aexp}  {s : state}  {stk : stack} :
exec (acomp a) (0, s, stk) (list.length (acomp a), s, (eval a s) :: stk) :=
begin
  induction a generalizing stk,
  case num {  --DONE
    simp [acomp, eval],
    apply rtc.star.single,
    apply exec1I,
    {
      simp [nth],
      simp[iexec],
    },
    {
      linarith,
    },
    {
      simp,
    }
  },
  case var {  --DONE
    simp [acomp, eval],
    apply rtc.star.single,
    apply exec1I,
    {
      simp [nth],
      simp[iexec],
    },
    {
      linarith,
    },
    {
      simp,
    }
  },
  case add : a b a_i b_i{ --DONE
    simp [acomp],
    --trans a ++ (b ++ [OP])
    apply exec_append_trans,
    apply int.of_nat(list.length (acomp a)),
    exact a_i,
    simp,
    {
      have h_b_add : exec (acomp b ++ [ADD]) (↑(list.length (acomp a)) - ↑(list.length (acomp a)), s, eval a s :: stk) (list.length (acomp b) + 1, s, eval (add a b) s :: stk) := 
      begin
        simp,
        --trans b ++ [OP]
        apply exec_append_trans,
        apply int.of_nat(list.length (acomp b)),
        exact b_i,
        simp,
        {
          simp,
          have h_add: exec [ADD] (0, s, eval b s :: eval a s :: stk) (1, s, eval (add a b) s :: stk) := 
          begin
            apply rtc.star.single,
            apply exec1I,
            {
              simp [nth, iexec, eval],
            },
            linarith,
            simp,
          end,
          exact h_add,
        },
        refl,
      end,
      exact h_b_add,
    },
    refl,
  },
  case sub : a b a_i b_i{ --DONE
    simp [acomp],
    --trans a ++ (b ++ [OP])
    apply exec_append_trans,
    apply int.of_nat(list.length (acomp a)),
    exact a_i,
    simp,
    {
      have h_b_add : exec (acomp b ++ [SUB]) (↑(list.length (acomp a)) - ↑(list.length (acomp a)), s, eval a s :: stk) (list.length (acomp b) + 1, s, eval (sub a b) s :: stk) := 
      begin
        simp,
        --trans b ++ [OP]
        apply exec_append_trans,
        apply int.of_nat(list.length (acomp b)),
        exact b_i,
        simp,
        {
          simp,
          have h_add: exec [SUB] (0, s, eval b s :: eval a s :: stk) (1, s, eval (sub a b) s :: stk) := 
          begin
            apply rtc.star.single,
            apply exec1I,
            {
              simp [nth, iexec, eval],
            },
            linarith,
            simp,
          end,
          exact h_add,
        },
        refl,
      end,
      exact h_b_add,
    },
    refl,
  },
  case mul : a b a_i b_i{ --DONE
    simp [acomp],
    --trans a ++ (b ++ [OP])
    apply exec_append_trans,
    apply int.of_nat(list.length (acomp a)),
    exact a_i,
    simp,
    {
      have h_b_add : exec (acomp b ++ [MUL]) (↑(list.length (acomp a)) - ↑(list.length (acomp a)), s, eval a s :: stk) (list.length (acomp b) + 1, s, eval (mul a b) s :: stk) := 
      begin
        simp,
        --trans b ++ [OP]
        apply exec_append_trans,
        apply int.of_nat(list.length (acomp b)),
        exact b_i,
        simp,
        {
          simp,
          have h_add: exec [MUL] (0, s, eval b s :: eval a s :: stk) (1, s, eval (mul a b) s :: stk) := 
          begin
            apply rtc.star.single,
            apply exec1I,
            {
              simp [nth, iexec, eval],
            },
            linarith,
            simp,
          end,
          exact h_add,
        },
        refl,
      end,
      exact h_b_add,
    },
    refl,
  },
  case div : a b a_i b_i{ --DONE
    simp [acomp],
    --trans a ++ (b ++ [OP])
    apply exec_append_trans,
    apply int.of_nat(list.length (acomp a)),
    exact a_i,
    simp,
    {
      have h_b_add : exec (acomp b ++ [DIV]) (↑(list.length (acomp a)) - ↑(list.length (acomp a)), s, eval a s :: stk) (list.length (acomp b) + 1, s, eval (div a b) s :: stk) := 
      begin
        simp,
        --trans b ++ [OP]
        apply exec_append_trans,
        apply int.of_nat(list.length (acomp b)),
        exact b_i,
        simp,
        {
          simp,
          have h_add: exec [DIV] (0, s, eval b s :: eval a s :: stk) (1, s, eval (div a b) s :: stk) := 
          begin
            apply rtc.star.single,
            apply exec1I,
            {
              simp [nth, iexec, eval],
            },
            linarith,
            simp,
          end,
          exact h_add,
        },
        refl,
      end,
      exact h_b_add,
    },
    refl,
  
  },

end


/-
fun bcomp :: "bexp ⇒ bool ⇒ int ⇒ instr list" where
"bcomp (Bc v) f n = (if v=f then [JMP n] else [])" |
"bcomp (Not b) f n = bcomp b (¬f) n" |
"bcomp (And b1 b2) f n =
 (let cb2 = bcomp b2 f n;
        m = if f then size cb2 else (size cb2)+n;
      cb1 = bcomp b1 False m
  in cb1 @ cb2)" |
"bcomp (Less a1 a2) f n =
 acomp a1 @ acomp a2 @ (if f then [JMPLESS n] else [JMPGE n])"

value
  "bcomp (And (Less (V ''x'') (V ''y'')) (Not(Less (V ''u'') (V ''v''))))
     False 3"
-/

inductive bexp : Type
| Bc : Prop → bexp
| Not : bexp → bexp
| And : bexp → bexp → bexp
| Less : aexp → aexp → bexp

open bexp
def bval : bexp → state → Prop
| (Bc v) s    := v
| (Not b) s   := ¬(bval b s)
| (And b1 b2) s := bval b1 s ∧ bval b2 s
| (Less a1 a2) s := (eval a1 s) < (eval a2 s) 

noncomputable def bcomp : bexp → Prop → ℤ → list instr  --TODO: TD6: find out whether noncomputable is okay
| (Bc v) f n := if (v = f) then [JMP n] else []
| (Not b) f n :=  bcomp b (¬ f) n
| (And b1 b2) f n := 
    let cb2 := bcomp b2 f n,
      m := if (f = true) then int.of_nat (list.length cb2) else int.of_nat (list.length cb2) + n,
      cb1 := bcomp b1 ff m
    in cb1 ++ cb2
| (Less a1 a2) f n := acomp a1 ++ acomp a2 ++ 
  (if (f = true) then [JMPLESS n] else [JMPGE n])

/-
lemma bcomp_correct[intro]:
  fixes n :: int
  shows
  "0 ≤ n ⟹
  bcomp b f n ⊢
 (0,s,stk)  →*  (size(bcomp b f n) + (if f = bval b s then n else 0),s,stk)"
proof(induction b arbitrary: f n)
  case Not
  from Not(1)[where f="~f"] Not(2) show ?case by fastforce
next
  case (And b1 b2)
  from And(1)[of "if f then size(bcomp b2 f n) else size(bcomp b2 f n) + n" 
                 "False"] 
       And(2)[of n f] And(3) 
  show ?case by fastforce
qed fastforce+
-/

lemma not_not_eq {α β : Prop}
(h_not_eq : ¬ (α = β)) :
α = ¬ β :=
begin
  rw [eq_iff_iff] at *,
  rw [not_iff] at h_not_eq,
  apply iff.not_right,
  exact h_not_eq,
end

lemma bcomp_Bc_correct {n :ℤ} {b f s stk} --TODO: fix list.nil edgecase
(h_nneg : 0 ≤ n) :
exec (bcomp (Bc b) f n) (0, s, stk) (↑(list.length (bcomp (Bc b) f n)) + ite (f = bval (Bc b) s) n 0, s, stk) :=
begin 
  apply rtc.star.single,
    simp [bcomp],
    rw [bval],
    by_cases h_bisf : (b = f),
    {
      simp [h_bisf],
      apply exec1I,
      {simp [nth],simp[iexec],},
      {linarith,},
      {simp,}
    },
    {
      simp [h_bisf],
      have h_fnotb : ¬ f = b := by cc, 
      simp [h_fnotb],
      apply exec1I,
      {simp [nth], simp [iexec],},
      {linarith,},
      {simp, sorry} --TODO: TD1: this is an edgecase because list.nil (or NOP) does not increase pc and such list.length [] cannot be > 0.
    }
end

lemma bcomp_correct {n: ℤ} { b f s stk}
(h_nneg : 0 ≤  n) :
exec (bcomp b f n) (0, s, stk) (list.length (bcomp b f n) + (if (f = bval b s) then n else 0), s, stk) :=
begin
  induction b generalizing f n,
  case Bc { --INCOMPLETE: list.nil edgecase
    apply bcomp_Bc_correct,
    apply h_nneg,
  },
  case Not : b{ --DONE
    specialize b_ih h_nneg,
    apply ¬ f,
    -- apply rtc.star.single,
    simp [bcomp],
    rw [bval],
    by_cases h_bisf : (f = bval b s),
    {
      simp [h_bisf],
      rw [h_bisf] at b_ih,
      simp * at b_ih,
      exact b_ih,
    },
    {
      have h_fneg : f = ¬ bval b s := 
      begin
        apply not_not_eq,
        exact h_bisf,
      end,
      simp [h_fneg],
      rw [h_fneg] at b_ih,
      simp * at b_ih,
      exact b_ih,
    }
  },
  case And : b1 b2 ih1 ih2{ --INCOMPLETE: structure of the proof? 
    -- specialize ih1 h_nneg,
    -- apply f,
    -- specialize ih2 h_nneg,
    -- apply f,
    simp [bcomp],
    rw [bval],
    by_cases h_b1 : (bval b1 s),
    {
      by_cases h_b2 : (bval b2 s),
      { -- bval b1 s ∧ bval b2 s
        
        sorry,
      },
      {-- bval b1 s ∧ ¬ bval b2 s
        sorry,
      }
    },
    {
      by_cases h_b2 : (bval b2 s),
      {-- ¬ bval b1 s ∧ bval b2 s
        sorry,
      },
      {-- ¬ bval b1 s ∧ ¬ bval b2 s
        sorry,
      }
    }
    -- by_cases h_ite : (f = bval b1 s ∧ bval b2 s),
    -- {
    --   by_cases h_b2 : (bval b2 s),
    --   {
    --     have h_b1_f : f = bval b1 s :=
    --     begin
    --       simp [h_b2] at h_ite,
    --       simp,
    --       apply h_ite,
    --     end,
    --     by_cases hf : (f = true),
    --     {sorry,},
    --     sorry,
    --   },
    --   {
    --     have hf : f = false :=
    --     begin
    --       simp [h_b2] at h_ite,
    --       apply false.elim,
    --       apply h_ite,
    --     end,
    --     simp [hf, h_ite],
    --     have hf_t : ¬ f = true :=
    --     begin
    --       simp [hf],
    --     end, 
    --     simp [hf_t],
    --     apply exec_append_trans,
    --     apply int.of_nat (list.length (bcomp b1 false (↑(list.length (bcomp b2 (bval b1 s) n)) + n))),
    --     {
    --       have h_bcomp : exec (bcomp b1 false (↑(list.length (bcomp b2 (bval b1 s) n)) + n)) (0, s, stk) (↑(list.length(bcomp b1 false (↑(list.length (bcomp b2 (bval b1 s) n)) + n))), s, stk) :=
    --       begin
    --       sorry,  -- this part does not make sense to me
    --       end,
    --       apply h_bcomp,
    --     },
    --     simp,
    --     {
    --       simp,
    --       have h_bcomp_b2 : exec (bcomp b2 (bval b1 s) n) (0, s, stk) (↑(list.length (bcomp b2 (bval b1 s) n)) + n, s, stk) :=
    --       begin
    --         have h_b2_f : f = bval b2 s :=
    --         begin
    --           simp [h_b2, hf],
    --         end,
    --         simp [h_b2_f] at ih2,
    --         simp [h_b2] at ih2,
    --         by_cases h_b1 : (bval b1 s),
    --         {
    --           simp [h_b1],  -- how to unify false and true in this case?
    --           sorry, 
    --         },
    --         {
    --           simp [h_b1],
    --           apply ih2,
    --         }
    --       end,
    --       apply h_bcomp_b2,
    --     },
    --     finish,
    --   },
    -- },
    -- {
    --   sorry,
    -- }
    -- by_cases hf : (f = true),
    -- {
    --   -- simp at *,
    --   -- simp [hf] at ih1 ih2,
    --   simp [hf],

    --   apply exec_append_trans,
    --   apply int.of_nat (list.length (bcomp b1 false ↑(list.length (bcomp b2 true n)))),
    --   {
    --     have h_b1_f_b2_t: exec (bcomp b1 false ↑(list.length (bcomp b2 true n))) (0, s, stk) (int.of_nat (list.length (bcomp b1 false ↑(list.length (bcomp b2 true n)))), s, stk) :=
    --     begin
    --       simp,

    --     sorry,
    --     end,
    --     exact h_b1_f_b2_t,
    --   },
    --   simp,
    --   {
    --     simp,
    --     have b2_t : exec (bcomp b2 true n) (0, s, stk) (↑(list.length (bcomp b2 true n)) + ite (f = (bval b1 s ∧ bval b2 s)) n 0, s, stk) :=
    --     begin
    --       by_cases h_ite : (f = (bval b1 s ∧ bval b2 s)),
    --       {
    --         simp [h_ite],
    --         simp [hf] at ih1 ih2 h_ite,
    --         have h_right : (f = bval b2 s) :=
    --         begin
    --           simp [h_ite.right],
    --           simp [hf],
    --         end,
    --         simp [h_right] at ih2,
    --         exact ih2,
    --       },
    --       {
    --         simp [h_ite],
    --         simp [hf] at ih1 ih2 h_ite,
    --         by_cases h_b1 : (bval b1 s),
    --         {
    --           simp [h_b1] at h_ite,
    --           have h_right_false : ¬ (f = bval b2 s) :=
    --           begin
    --             simp [hf, h_ite],
    --           end,
    --           simp [h_right_false] at ih2,
    --           exact ih2,
    --         },  
    --         {
    --           have h_right_false : ¬ (f = bval b2 s) :=
    --           begin
    --             simp [hf, h_ite],
    --             sorry, -- since h_b1 is false, i cannot use it to get ¬ bval b2 s - HOW?
    --           end,
    --           simp [h_right_false] at ih2,
    --           exact ih2,
    --         },
    --       }
    --     end,
    --     exact b2_t,
    --   },
    --   finish,-- TODO: TD3: have an exec not like ih but (bcomp b1 false (↑(list.length (bcomp b2 false n)) + n))
    -- },
    -- {
    --   simp [hf],
    --   have h_f_false : f = ¬true :=
    --   begin
    --     apply not_not_eq, 
    --     exact hf,
    --   end,
    --   simp at h_f_false,
    --   apply exec_append_trans,
    --   apply int.of_nat (list.length (bcomp b1 false ↑(list.length (bcomp b2 true n)))),
    --   {
    --     have h_b1_f_b2_t: exec (bcomp b1 false (↑(list.length (bcomp b2 f n)) + n)) (0, s, stk) (int.of_nat (list.length (bcomp b1 false (↑(list.length (bcomp b2 f n)) + n))), s, stk) :=
    --     begin
    --       simp,

    --     sorry,
    --     end,
    --     exact h_b1_f_b2_t,
    --   },
    --   simp,
    --   {
    --     simp,
    --     have b2_t : exec (bcomp b2 true n) (0, s, stk) (↑(list.length (bcomp b2 true n)) + ite (f = (bval b1 s ∧ bval b2 s)) n 0, s, stk) :=
    --     begin
    --       by_cases h_ite : (f = (bval b1 s ∧ bval b2 s)),
    --       {
    --         simp [h_ite],
    --         simp [h_f_false] at ih1 ih2 h_ite,
    --         have h_right : (f = bval b2 s) :=
    --         begin
    --           sorry,
    --         end,
    --         simp [h_right] at ih2,
    --         exact ih2,
    --       },
    --       {
    --         simp [h_ite],
    --         simp [hf] at ih1 ih2 h_ite,
    --         by_cases h_b1 : (bval b1 s),
    --         {
    --           simp [h_b1] at h_ite,
    --           have h_right_false : ¬ (f = bval b2 s) :=
    --           begin
    --             simp [hf, h_ite],
    --           end,
    --           simp [h_right_false] at ih2,
    --           exact ih2,
    --         },  
    --         {
    --           have h_right_false : ¬ (f = bval b2 s) :=
    --           begin
    --             simp [hf, h_ite],
    --             sorry, -- since h_b1 is false, i cannot use it to get ¬ bval b2 s - HOW?
    --           end,
    --           simp [h_right_false] at ih2,
    --           exact ih2,
    --         },
    --       }
    --     end,
    --     exact b2_t,
    --   },
    --   finish,-- TODO: TD3: have an exec not like ih but (bcomp b1 false (↑(list.length (bcomp b2 false n)) + n))
    -- }
  },
  case Less : a1 a2{  --DONE
    simp [bcomp],
    rw [bval],
    -- acomp a1 ++ (acomp a2 ++ ite (f = true) [JMPLESS n] [JMPGE n])
    apply exec_append_trans,
    apply int.of_nat (list.length (acomp a1)),
    apply acomp_correct,
    simp,
    {
      simp,
      have h_a2_ite : exec (acomp a2 ++ ite (f = true) [JMPLESS n] [JMPGE n]) (0, s, eval a1 s :: stk) ((↑(list.length (acomp a2)) + ↑(list.length (ite (f = true) [JMPLESS n] [JMPGE n]))) +
        ite (f = (eval a1 s < eval a2 s)) n 0, s, stk) := 
      begin
        -- (acomp a2 ++ ite (f = true) [JMPLESS n] [JMPGE n])
        apply exec_append_trans,
        apply int.of_nat (list.length (acomp a2)),
        apply acomp_correct,
        simp,
        {
          simp,
          have h_ite : exec (ite (f = true) [JMPLESS n] [JMPGE n]) (0, s, eval a2 s :: eval a1 s :: stk) (↑(list.length (ite (f = true) [JMPLESS n] [JMPGE n])) + ite (f = (eval a1 s < eval a2 s)) n 0, s, stk) := 
          begin
            by_cases h_f : (f = true),
            { -- [JMPLESS]
              simp [h_f],
              apply rtc.star.single,
              apply exec1I,
              {
                simp [nth],
                simp [iexec],
                by_cases h_ite : (eval a1 s < eval a2 s),
                {simp [h_ite],},
                {simp [h_ite],}
              },
              simp,
              simp,
            },
            { -- [JMPGE]
              simp [h_f],
              apply rtc.star.single,
              apply exec1I,
              {
                simp [nth],
                simp [iexec],
                have h_f_false : f = ¬ true :=
                begin
                  apply not_not_eq,
                  exact h_f,
                end,
                simp [h_f_false],
                by_cases h_ite : (eval a2 s ≤ eval a1 s),
                {simp [h_ite],},
                {simp [h_ite],}
              },
              simp,
              simp,
            },
          end,
          exact h_ite,
        },
        finish,
      end,
      exact h_a2_ite,
    },
    finish,
  }

end



/-
fun ccomp :: "com ⇒ instr list" where
"ccomp SKIP = []" |
"ccomp (x ::= a) = acomp a @ [STORE x]" |
"ccomp (c⇩1;;c⇩2) = ccomp c⇩1 @ ccomp c⇩2" |
"ccomp (IF b THEN c⇩1 ELSE c⇩2) =
  (let cc⇩1 = ccomp c⇩1; cc⇩2 = ccomp c⇩2; cb = bcomp b False (size cc⇩1 + 1)
   in cb @ cc⇩1 @ JMP (size cc⇩2) # cc⇩2)" |
"ccomp (WHILE b DO c) =
 (let cc = ccomp c; cb = bcomp b False (size cc + 1)
  in cb @ cc @ [JMP (-(size cb + size cc + 1))])"


value "ccomp
 (IF Less (V ''u'') (N 1) THEN ''u'' ::= Plus (V ''u'') (N 1)
  ELSE ''v'' ::= V ''u'')"

value "ccomp (WHILE Less (V ''u'') (N 1) DO (''u'' ::= Plus (V ''u'') (N 1)))"
-/

inductive com : Type
| SKIP : com
| Assign : vname → aexp → com
| Seq : com → com → com
| If : bexp → com → com → com
| While : bexp → com → com

open com

noncomputable def ccomp : com → list instr
| com.SKIP := []
| (Assign x a) := acomp a ++ [STORE x]
| (Seq c1 c2) := ccomp c1 ++ ccomp c2
| (If b c1 c2) := (
  let cc1 := ccomp c1,
    cc2 := ccomp c2,
    cb := bcomp b false (list.length cc1 + 1)
  in cb ++ cc1 ++ (JMP (list.length cc2) :: cc2)
)
| (While b c) := (
  let cc := ccomp c,
    cb := bcomp b false (list.length cc + 1)
  in cb ++ cc ++ [JMP (-(list.length cb + list.length cc + 1))] 
)
open com

infixr ` ;; ` : 90 := Seq

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


-- lemma silly_loop_from_1_big_step : --TODO: TD5: silly_loop notation clarification
--   (silly_loop ({"x" ↦ 1}) {"x" ↦ 1}) ⟹ (λ_, 0) :=
-- begin
--   rw silly_loop,
--   apply big_step.while_true,
--   { simp },
--   { apply big_step.seq,
--     { apply big_step.skip },
--     { apply big_step.assign } },
--   { simp,
--     apply big_step.while_false,
--     linarith }
-- end


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

lemma big_step_terminates {S s} :
  ∃t, (S, s) ⟹ t :=
sorry   -- unprovable

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



/-

subsection "Preservation of semantics"

lemma ccomp_bigstep:
  "(c,s) ⇒ t ⟹ ccomp c ⊢ (0,s,stk) →* (size(ccomp c),t,stk)"
proof(induction arbitrary: stk rule: big_step_induct)
  case (Assign x a s)
  show ?case by (fastforce simp:fun_upd_def cong: if_cong)
next
  case (Seq c1 s1 s2 c2 s3)
  let ?cc1 = "ccomp c1"  let ?cc2 = "ccomp c2"
  have "?cc1 @ ?cc2 ⊢ (0,s1,stk) →* (size ?cc1,s2,stk)"
    using Seq.IH(1) by fastforce
  moreover
  have "?cc1 @ ?cc2 ⊢ (size ?cc1,s2,stk) →* (size(?cc1 @ ?cc2),s3,stk)"
    using Seq.IH(2) by fastforce
  ultimately show ?case by simp (blast intro: star_trans)
next
  case (WhileTrue b s1 c s2 s3)
  let ?cc = "ccomp c"
  let ?cb = "bcomp b False (size ?cc + 1)"
  let ?cw = "ccomp(WHILE b DO c)"
  have "?cw ⊢ (0,s1,stk) →* (size ?cb,s1,stk)"
    using ‹bval b s1› by fastforce
  moreover
  have "?cw ⊢ (size ?cb,s1,stk) →* (size ?cb + size ?cc,s2,stk)"
    using WhileTrue.IH(1) by fastforce
  moreover
  have "?cw ⊢ (size ?cb + size ?cc,s2,stk) →* (0,s2,stk)"
    by fastforce
  moreover
  have "?cw ⊢ (0,s2,stk) →* (size ?cw,s3,stk)" by(rule WhileTrue.IH(2))
  ultimately show ?case by(blast intro: star_trans)
qed fastforce+

end
-/


lemma ccomp_bigstep {c : com} { s : state } {t : state } {stk : stack} 
(h_step : (c, s) ⟹ t) :
exec (ccomp c) (0, s, stk) (list.length (ccomp c), t, stk) :=
begin
induction c generalizing stk,
  case SKIP { --INCOMPLETE: list.nil problem
    apply rtc.star.single,
    simp [ccomp],
    apply exec1I,
    {simp [nth], simp [iexec], finish,},
    {linarith,},
    {simp, sorry} --TODO: TD1: this is an edgecase because list.nil (or NOP) does not increase pc and such list.length [] cannot be > 0.
  },
  case Assign : v a{  --DONE
    simp [ccomp],
    apply exec_append_trans,
    apply int.of_nat (list.length (acomp a)),
    apply acomp_correct,
    simp,
    {
      simp,
      have h_store : exec [STORE v] (0, s, eval a s :: stk) (int.of_nat (list.length ([STORE])), t, stk) :=
      begin
        apply rtc.star.single,
        apply exec1I,
        {
          simp [nth],
          simp [iexec],
          finish,
        },
        {simp,},
        {simp,}
      end,
      exact h_store,
    },
    simp,
  },
  case Seq : c1 c2 ch1 ch2 {  -- INCOMPLETE: h_step problem
    simp [ccomp],
    simp [big_step_seq_iff] at h_step,  
    cases h_step with u u_steps,    --TODO: TD4: How to specify this step exactly to t?
    apply exec_append_trans,
    apply int.of_nat (list.length (ccomp c1)),
    apply ch1,
    { -- prove (c1, s) ⟹ t
      sorry,
    },
    simp,
    {
      simp,
      have h_ccomp2 : exec (ccomp c2) (0, t, stk) (↑(list.length (ccomp c2)), t, stk) :=
      begin
        -- set the c1 step up to t and this t to t 
        sorry,
      end,
      exact h_ccomp2,
    },
    refl,
  },
  case If : cond c1 c2 ch1 ch2 {  --INCOMPLETE: stuck on h_step and exec_cons_1, and bcomp cond
    simp [ccomp],
    -- ↑(list.length (bcomp cond false (↑(list.length (ccomp c1)) + 1))) + (↑(list.length (ccomp c1)) + (↑(list.length (ccomp c2)) + 1))
    apply exec_append_trans,
    apply int.of_nat (list.length (bcomp cond false (↑(list.length (ccomp c1)) + 1))),
    {
      have h_bcomp : exec (bcomp cond false (↑(list.length (ccomp c1)) + 1)) (0, s, stk) (int.of_nat (list.length (bcomp cond false (↑(list.length (ccomp c1)) + 1))), s, stk) := 
      begin 
        -- apply bcomp_correct,
        sorry,
      end,
      exact h_bcomp,
    },
    simp,
    {
      simp,
      have h_ccomp_jmp : exec (ccomp c1 ++ JMP ↑(list.length (ccomp c2)) :: ccomp c2) (0, s, stk) ((↑(list.length (ccomp c1)) + (↑(list.length (ccomp c2)) + 1)), t, stk) :=
      begin 
        apply exec_append_trans,
        apply int.of_nat (list.length (ccomp c1)),
        {
          have h_ccomp1 : exec (ccomp c1) (0, s, stk) (↑(list.length (ccomp c1)), t, stk) :=
          begin
            apply ch1,
            simp at h_step,
            --TODO: extract (c1, s) ⟹ t from h_step
            by_cases h_cond: (bval cond s),
            {
              simp [h_cond] at h_step,
              apply h_step,
            },
            {
              simp [h_cond] at h_step,
              sorry,  -- this is the false case and i don't know how to handle it
            },
          end,
          exact h_ccomp1,
        },
        simp,
        {
          simp,
          have h_jmp : exec (JMP ↑(list.length (ccomp c2)) :: ccomp c2) (0, t, stk) ((↑(list.length (ccomp c2)) + 1), t, stk) :=
          begin
            sorry, -- exec_cons_1 but it does not work due to being from 1 not from 0
          end,
          exact h_jmp,
        },
        simp,
      end,
      exact h_ccomp_jmp,
    },
    simp,
  },
  case While : cond c ch{  --INCOMPLETE: bcomp reduce and h_step dependancy on bcond and jmp i calculation
    simp [ccomp],
    -- ↑(list.length (bcomp cond false (↑(list.length (ccomp c)) + 1))) + (↑(list.length (ccomp c)) + 1)
    apply exec_append_trans,
    apply int.of_nat (list.length (bcomp cond false (↑(list.length (ccomp c)) + 1))),
    {
      have h_cond : exec (bcomp cond false (↑(list.length (ccomp c)) + 1)) (0, s, stk) (↑(list.length (bcomp cond false (↑(list.length (ccomp c)) + 1))), s, stk) :=
      begin
        apply rtc.star.single,
        --reduce bcomp here
        sorry,
      end,
      exact h_cond,
    },
    simp,
    {
      simp,
      have h_body : exec (ccomp c ++ 
          [JMP (-1 + (-↑(list.length (ccomp c)) + -↑(list.length (bcomp cond false (↑(list.length (ccomp c)) + 1)))))])
          (0, s, stk) ((↑(list.length (ccomp c)) + 1), t, stk) :=
      begin
        apply exec_append_trans,
        apply int.of_nat (list.length (ccomp c)),
        {
          have h_ccomp : exec (ccomp c) (0, s, stk) (↑(list.length (ccomp c)), t, stk) :=
          begin
            apply ch,
            --extract (c, s) ⟹ t from h_step using bcond true/false dependency
            sorry,
          end,
          exact h_ccomp,
        },
        simp,
        {
          simp,
          have h_jmp : exec (
          [JMP (-1 + (-↑(list.length (ccomp c)) + -↑(list.length (bcomp cond false (↑(list.length (ccomp c)) + 1)))))])
          (0, t, stk) ( -↑(list.length (ccomp c)) + -↑(list.length (bcomp cond false (↑(list.length (ccomp c)) + 1))) , t, stk) :=
          begin
            apply rtc.star.single,
            apply exec1I,
            {
              simp [nth, iexec],
            },
            simp,
            simp,
          end,
          exact h_jmp,
        },
        simp,
        sorry,
      end,
      exact h_body,
    },
    simp,
  },
end



/-
QUESTIONS:
TD1 : How to solve an edgecase for NOP?: 
      0 < ↑(list.length list.nil) - this is an edgecase because list.nil (or NOP) does not increase pc and such list.length [] cannot be > 0.
      (bcomp Bc and ccomp SKIP)  
TD3 : bcomp and - how to get a correct exec?
TD4 : How to specify this step exactly to t?
TD5 : silly loop notation clarification? - not important
TD6: noncomputable - is it correct? - not important
TD7: Do I need to do small_step semantics? they are not in the .thy file but are in the chapter 8
-/
end LoComp
