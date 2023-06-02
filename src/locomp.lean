import .defs
import .exec
import .comp_def
import .big_step

namespace LoComp

open instr
open aexp
open bexp
open com

/-
declare Let_def[simp]


subsection "Compilation"


-/
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

lemma bcomp_Bc_correct (n :ℤ) (b f s stk) --TODO: fix list.nil edgecase
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

lemma bcomp_correct (n: ℤ) ( b f s stk)
(h_nneg : 0 ≤  n) :
exec (bcomp b f n) (0, s, stk) (list.length (bcomp b f n) + (if (f = bval b s) then n else 0), s, stk) :=
begin
  induction b generalizing f n,
  case Bc { --INCOMPLETE: list.nil edgecase
    apply bcomp_Bc_correct,
    apply h_nneg,
  },
  case Not : b{ --DONE
    specialize b_ih (¬f) n,
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
    specialize ih1 false (↑(list.length (bcomp b2 f n)) + ite (f = bval b2 s) n 0),
    have h_b2_len_nneg : 0 ≤ (↑(list.length (bcomp b2 f n)) + ite (f = bval b2 s) n 0) :=
    begin
      have h_b2_len : 0 ≤ ↑(list.length (bcomp b2 f n)) := by simp [list.length_nneg],
      have h_ite_leng : 0 ≤  ite (f = bval b2 s) n 0 := begin
        by_cases h_ite : (f = bval b2 s),
        {
          simp [h_ite],
          apply h_nneg,
        },
        {simp [h_ite],}
      end,
      linarith,
    end,
    simp [h_b2_len_nneg] at ih1,
    specialize ih2 f n,
    simp [h_nneg] at ih2,

    simp [bcomp],
    by_cases h_f : (f = true),
    {
      simp [h_f],
      sorry,
    },
    {
      simp [h_f],
      sorry,
    }
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
