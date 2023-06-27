import .defs

namespace LoComp

open instr
/- # Verification infrastructure -/

/-
  ## iexec shift lemma
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


/- ## exec concatenation correctness -/
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
  ## Additional exec concatenation lemmas
-/
lemma exec_cons_1 {s stk j t stk' li instr}
(h_li : exec li (0, s, stk) (j, t, stk')):
exec (instr :: li) (1, s, stk) (1 + j, t, stk') :=
begin 
  have h_shift : exec ([instr] ++ li) ((list.length [instr]) + 0, s, stk) ((list.length [instr]) + j, t, stk') :=
  begin 
    apply exec_appendL,
    apply j,
    apply j,
    apply h_li,
  end,
  simp at h_shift,
  exact h_shift,
end

lemma exec_appendL_if {li' li s stk j s' stk'} {i i' : ℤ}
(h_more: int.of_nat (list.length li') <= i )
(h_li: exec li (i - list.length li', s, stk) (j, s', stk'))
(h_i': i' = list.length li' + j): 
exec (li' ++ li) (i, s, stk) (i', s', stk') :=
begin
  have h_append : exec (li' ++ li) (list.length li' + (i - list.length li'), s, stk) (list.length li' + j, s', stk') :=
  begin
    apply exec_appendL,
    apply i,
    apply i,
    apply h_li,
  end,
  simp at h_append,
  rw [h_i'],
  exact h_append,
end

/-
  ### Splitting the execution into execution of parts
-/
lemma exec_append_trans {li' li s stk  s' stk' s'' stk''} {i i' j'' i'': ℤ}
(h_li: exec li (0, s, stk) (i', s', stk'))
(h_i': int.of_nat (list.length li) <= i' )
(h_li': exec li' (i' - list.length li, s', stk') (i'', s'', stk''))
(h_j'': j'' = list.length li + i''): 
exec (li ++ li') (0, s, stk) (j'', s'', stk'') :=
begin
  apply rtc.star.trans,
  have h_appendR_li' : exec (li ++ li') (0, s, stk) (i', s', stk') :=
  begin
    apply exec_appendR h_li,
  end, 
  exact h_appendR_li',
  have h_appendL_li : exec (li ++ li') (list.length li + (i' - list.length li), s', stk') (list.length li + i'', s'', stk'') :=
  begin
    apply exec_appendL,
    apply i',
    apply i',
    apply h_li',
  end,
  simp at h_appendL_li,
  rw [h_j''],
  exact h_appendL_li,
end

end LoComp