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
| ADD (i, s, stk) := (i + 1, s, (head2 stk + stk.head) :: tail2 stk)
| SUB (i, s, stk) := (i + 1, s, (head2 stk - stk.head) :: tail2 stk)
| MUL (i, s, stk) := (i + 1, s, (head2 stk * stk.head) :: tail2 stk)
| DIV (i, s, stk) := (i + 1, s, (head2 stk / stk.head) :: tail2 stk)
| (STORE v) (i, s, stk) := (i + 1, s{v ↦ (stk.head)}, stk.tail)
| (JMP n) (i, s, stk) := (i + 1 + n, s, stk)
| (JMPLESS n) (i, s, stk) := 
  if (head2 stk) < (stk.head)
  then (i + 1 + n, s, tail2 stk)
  else (i + 1, s, tail2 stk)
| (JMPGE n) (i, s, stk) := 
  if (head2 stk) ≥ (stk.head)
  then (i + 1 + n, s, tail2 stk)
  else (i + 1, s, tail2 stk)
| NOP (i, s, stk) := (i + 1, s, stk)

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
(∃ i s stk, c = (i, s, stk) ∧ c' = iexec (nth li i) (i, s, stk) ∧ 0 ≤ i ∧ i < li.length)  

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
    use i,
    use s,
    use stk,
    simp [h1, h2, h3]
  end

-- lemma exec_trans {li : list instr} {c1 c2 c3 : config}
--   (h1 : exec1 li c1 c2)
--   (h2 : exec1 li c2 c3) :
--   exec1 li c1 c3 :=
--   begin
--     -- Use the definition of exec1 to unpack the assumptions

--     rcases h1 with ⟨i1, s1, stk1, hc1, hc2, hi1⟩,
--     rcases h2 with ⟨i2, s2, stk2, hc2', hc3, hi2⟩,
--     -- Use transitivity of execution to relate the two configurations
--     -- subst hc2,
--     have h : i1 < li.length,
--     { linarith [hi1, hi2] },
--     -- Apply exec1I lemma to obtain the transitivity lemma
--     -- exact exec1I hc3 hi1.left h,
--     sorry
--     -- TODO: replace exec1 right side of c3 with h1 items 
--   end




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
    intros h1 h2,
    apply iexec_shift_without_jmp,
  },
end


@[simp]
theorem list.zero_le_length {α : Type} (l : list α) : 0 ≤ list.length l :=
begin
  induction l with hd tl hl,
  case list.nil { simp,},
  { simp [list.length_cons, int.coe_nat_succ],}
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
          cases i,
          {
            cases i,
            {
              simp at h_izero,
              cc,
            },
            {
              rw [int.of_nat_succ],
              simp,
            }
            
          },
          {
            simp [h_izero],
            simp at h_nneg,
            apply h_nneg,
          }
        },
      }
    },
    {
      simp only [h_ite],
      simp,
      by_cases h_izero : (i = 0),
      {
        specialize l1_ih h_nneg,
        simp [h_izero] at *,
        simp [nth] at *,
        -- the goal expects l1_hd to be reachable by l2 at -i - l1_tl.length
        -- and i have no clue how to get to that so i should rewrite it
        sorry,
      },
      {
        -- specialize l1_ih h_nneg,
        simp [nth] at *,
        simp [h_izero],
        --TODO: specialize with i - 1, then i can do something maybe
        have h_notless : ¬ (i < list.length l1_tl) := by linarith,
        -- simp [h_notless] at l1_ih,
        -- ring_nf,
        -- rw ← [int.add_assoc],
        have h_iminusdist : i - (↑(list.length l1_tl) + 1) = i - 1 - ↑(list.length l1_tl) := 
        begin
          ring,
        end,
        simp [h_iminusdist],
        
        -- port i to i - 1, but don't know how to. Maybe cc
        sorry,
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
  obtain ⟨i, s, stk, hi, h_conds⟩ := h,
  induction li,
  case list.nil {
    -- simp,
    -- cases c with i s_stk,
    -- -- cases s_stk with s stk,
    use i,
    use s,
    use stk,
    unfold_coes, --for int.of_nat in the goal - types
    split,
    {
      apply hi,
    },
    simp at h_conds,
    have h_f : false, begin 
      have h_imore: 0 ≤ i, from h_conds.right.left,
      have h_iless: i < 0, from  h_conds.right.right,
      linarith,
    end,
    apply false.elim,
    show false, from h_f,
  },
  case list.cons {
    simp,
    use i,
    use s,
    use stk,
    ring_nf,
    norm_cast at *,
    unfold_coes,
    split,
    apply hi,
    have h_c' : c' = iexec (nth (li_hd :: (li_tl ++ li')) i) (i, s, stk) :=
      begin
        rw h_conds.left,

        sorry, -- do not know how to get this
      end,
    have h_ilow : 0 ≤ i, from h_conds.right.left, -- from h if possible to reverse exec1I
    have h_ihigh : i < (list.length li_tl + (list.length li' + 1)) :=
    begin
      have h_initial : i < list.length (li_hd :: li_tl), from h_conds.right.right, -- from the h
      have h_full : (list.length (li_hd :: li_tl)) ≤ ((list.length li_tl) + ((list.length li') + 1)) := by simp, -- from inequality def
      linarith,
    end,
    have h_bounds : 0 ≤ i ∧ i < ↑(list.length li_tl + (list.length li' + 1)), from and.intro h_ilow h_ihigh,
    show c' = iexec (nth (li_hd :: (li_tl ++ li')) i) (i, s, stk) ∧ 0 ≤ i ∧ i < (list.length li_tl + (list.length li' + 1)), from and.intro h_c' h_bounds,
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

lemma exec1_appendL {i i' :ℤ} {li li' i s stk i' s' stk'}
(h : exec1 li (i, s, stk) (i', s', stk')) :
exec1 (li' ++ li) ((list.length li') + i, s, stk) ((list.length li') + i', s', stk') :=
begin
  simp only [exec1],
  obtain ⟨i_h, s_h, stk_h, hi, h_conds⟩ := h,
  use i,
  use s,
  use stk,
  have h_i : i = i_h := by finish,
  have h_s : s = s_h := by finish,
  have h_stk : stk = stk_h := by finish,
  split,
  {

    sorry,  -- intuition that the pc was shifted by list.length(?) 
  },
  {
    fconstructor,
    {
      -- apply iexec_shift, and probably nth_append
      sorry,
    },
    norm_num,
    have h_ilow : 0 ≤ i :=
    begin
      subst h_i, 
      apply h_conds.right.left,
    end,
    have h_ihigh : i < list.length li' + list.length li :=
    begin
      have h_initial : i < list.length li := 
      begin 
        subst i_h,
        apply h_conds.right.right,
      end,
      have h_full : list.length li ≤ list.length li' + list.length li := by simp, -- from inequality def
      linarith,
    end,
    show 0 ≤ i ∧ i < list.length li' + list.length li, from and.intro h_ilow h_ihigh
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
-- lemma exec_appendL {i i'} 
lemma exec_appendL {i i' :ℤ} {li li' i s stk i' s' stk'}
(h_single : exec li (i, s, stk) (i', s', stk')) :
exec (li' ++ li) (list.length li' + i, s, stk) (list.length li' + i', s', stk') :=
begin
  induction' h_single,
  case LoComp.rtc.star.refl {
    fconstructor,
  },
  case LoComp.rtc.star.tail {
    -- apply rtc.star.tail,
    -- {
    --   sorry,
    -- },
    -- {
    --   apply exec1_appendR,
    --   exact h,
    -- },

sorry,  
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
  rw ← list.nil_append li at h,
  have h' : exec [instr] (0, s, stk) (1, s, stk),
  {
    sorry, 
  }, 

  -- induction li,
  

  -- exact h'',
  -- exact exec_appendL h,
  sorry,
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
  fconstructor,
  {apply (i, s, stk)},
  {sorry},
  {sorry},
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
lemma exec_appendL_trans {li' li s stk  s' stk' s'' stk''} {i i' j'' i'': ℤ}
(h1: exec li (0, s, stk) (i', s', stk'))
(h2: int.of_nat (list.length li) <= i' )
(h3: exec li' (i' - list.length li, s', stk') (i'', s'', stk''))
(h3: j'' = list.length li + 1): 
exec (li ++ li') (0, s, stk) (j'', s'', stk'') :=
begin
  sorry
end

/-
declare Let_def[simp]


subsection "Compilation"

fun acomp :: "aexp ⇒ instr list" where
"acomp (N n) = [LOADI n]" |
"acomp (V x) = [LOAD x]" |
"acomp (Plus a1 a2) = acomp a1 @ acomp a2 @ [ADD]"

lemma acomp_correct[intro]:
  "acomp a ⊢ (0,s,stk) →* (size(acomp a),s,aval a s#stk)"
by (induction a arbitrary: stk) fastforce+

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


end LoComp
