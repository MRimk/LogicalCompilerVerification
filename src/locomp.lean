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

# Compilation correctness

## acomp correctness
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

## bcomp correctness
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

lemma bcomp_correct (n: ℤ) ( b f s stk)
(h_nneg : 0 ≤  n) :
exec (bcomp b f n) (0, s, stk) (list.length (bcomp b f n) + (if (f = bval b s) then n else 0), s, stk) :=
begin
  induction b generalizing f n,
  case Bc { --DONE
    simp [bcomp],
    rw [bval],
    by_cases h_b_is_f : (b = f),
    {
      simp [h_b_is_f],
      apply rtc.star.single,
      apply exec1I,
      {simp [nth],simp[iexec],},
      {linarith,},
      {simp,}
    },
    {
      simp [h_b_is_f],
      have h_fnotb : ¬ f = b := by cc, 
      simp [h_fnotb],
      apply rtc.star.refl,
    }
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
  case And : b1 b2 ih1 ih2{ --DONE

    simp [bcomp, bval],
    by_cases h_f : (f = true),
    {
      simp [h_f],
      rw [bval],
      apply exec_append_trans,
      apply int.of_nat ((bcomp b1 false ↑((bcomp b2 true n).length)).length),
      {
        specialize ih1 false (int.of_nat (list.length (bcomp b2 f n))),
        simp at ih1,
        simp [h_f] at ih1,
        apply ih1,
      },
      simp,
      {
        by_cases h_b1 : (false = bval b1 s),
        simp [h_b1],
        simp [h_b1],
      },
      {
        simp,
        have h_last : exec (bcomp b2 true n) (ite (false = bval b1 s) ↑((bcomp b2 true n).length) 0, s, stk) (↑((bcomp b2 true n).length) + ite (f = (bval b1 s ∧ bval b2 s)) n 0, s, stk) :=
        begin
          by_cases (false = bval b1 s),
          {   
            have h_and_false : ¬ f = (bval b1 s ∧ bval b2 s) := 
            begin
              rw [h_f],
              rw [←h],
              simp,
            end, 
            simp [h_and_false],
            simp [h],
            have h_bcomp2 : exec (bcomp b2 true n) (↑((bcomp b2 true n).length), s, stk) (↑((bcomp b2 true n).length), s, stk) :=
            begin
              apply rtc.star.refl,
            end,
            -- length bcomp b2 - apply h_bcomp2
            apply h_bcomp2,
          },
          {
            simp [h],
            have h_rw_and : (bval b1 s ∧ bval b2 s) = (bval b2 s) := 
            begin
              have h_bval : bval b1 s := 
              begin
                have h_not_in : (false = ¬ (bval b1 s)) :=
                begin
                  apply not_not_eq,
                  apply h,
                end,
                simp at h_not_in,
                apply h_not_in,
              end,
              simp [h_bval],
            end,
            rw [h_rw_and], 
            specialize ih2 true n,
            simp [h_nneg] at ih2,
            -- 0 - apply ih2
            rw [h_f],
            apply ih2,
          },
        end,
        apply h_last,
        -- something is really not right here because if i move simp is not working here.
      },
      finish,
    },
    {
      simp [h_f],
      rw [bval],
      have h_imp_nneg : 0 ≤ ↑((bcomp b2 f n).length) + n := 
      begin
        have h_list_nneg : 0 ≤ ↑((bcomp b2 f n).length) :=
        begin
          simp [list.length_nneg],
        end,
        linarith,
      end,
      apply exec_append_trans,
      apply int.of_nat ((bcomp b1 false (↑((bcomp b2 f n).length) + n)).length),
      {
        specialize ih1 false (int.of_nat (list.length (bcomp b2 f n)) + n),
        simp at ih1,        
        simp [h_imp_nneg] at ih1,
        apply ih1,
      },
      simp,
      {
        by_cases h_b1 : (false = bval b1 s),
        {
          simp [h_b1],
          simp [h_imp_nneg],
        },
        simp [h_b1],
      },
      {

        simp,
        have h_last : exec (bcomp b2 f n) (ite (false = bval b1 s) (↑((bcomp b2 f n).length) + n) 0, s, stk) (↑((bcomp b2 f n).length) + ite (f = (bval b1 s ∧ bval b2 s)) n 0, s, stk) :=
        begin
          by_cases (false = bval b1 s),
          {   
            have h_and_false : f = (bval b1 s ∧ bval b2 s) := 
            begin
              have h_not_f : ¬ f := 
              begin
                have h_false : f = ¬true  := 
                begin
                  apply not_not_eq,
                  apply h_f,
                end,
                simp at h_false,
                apply h_false,
              end,
              have h_not_bval : ¬ bval b1 s := 
              begin
                simp at h,
                apply h,
              end,
              simp [h_not_f, h_not_bval],
            end, 
            simp [h_and_false],
            simp [h],
            have h_bcomp2 : exec (bcomp b2 (bval b1 s ∧ bval b2 s) n) (↑((bcomp b2 (bval b1 s ∧ bval b2 s) n).length) + n, s, stk) (↑((bcomp b2 (bval b1 s ∧ bval b2 s) n).length) + n, s, stk) :=
            begin
              apply rtc.star.refl,
            end,
            apply h_bcomp2,
            
            -- length bcomp b2 - apply h_bcomp2
          },
          {
            simp [h],
            have h_rw_and : (bval b1 s ∧ bval b2 s) = (bval b2 s) := 
            begin
              have h_bval : bval b1 s := 
              begin
                have h_not_in : (false = ¬ (bval b1 s)) :=
                begin
                  apply not_not_eq,
                  apply h,
                end,
                simp at h_not_in,
                apply h_not_in,
              end,
              simp [h_bval],
            end,
            rw [h_rw_and], 
            specialize ih2 f n,
            simp [h_nneg] at ih2,
            apply ih2,
            -- 0 - apply ih2
            
          },
        end,
        apply h_last,

      },
      {
        simp [int.add_assoc],
      }
    },
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

## Preservation of semantics

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


lemma ccomp_bigstep {c : com} { s : state } {t : state } (stk : stack) 
(h_step : (c, s) ⟹ t) :
exec (ccomp c) (0, s, stk) (list.length (ccomp c), t, stk) :=
begin
  induction' h_step,
  case skip { -- DONE
    simp [ccomp],
    apply rtc.star.refl,
  },
  case assign { -- DONE
    simp [ccomp],
    apply exec_append_trans,
    apply int.of_nat (list.length (acomp a)),
    apply acomp_correct,
    simp,
    {
      simp,
      have h_store : exec [STORE x] (0, t, eval a t :: stk) (int.of_nat (list.length ([STORE])), t{x ↦ eval a t}, stk) :=
      begin
        apply rtc.star.single,
        apply exec1I,
        {
          simp [nth],
          simp [iexec],
        },
        {simp,},
        {simp,}
      end,
      exact h_store,
    },
    simp,
  },
  case seq : c1 c2 s u t{ -- DONE
    simp [ccomp],
    apply exec_append_trans,
    apply int.of_nat ((ccomp c1).length),
    apply ih_h_step,
    simp,
    {
      simp,
      apply ih_h_step_1,
    },
    simp,
  },
  case ite_true : b c1 c2 { --DONE
    simp [ccomp],
      apply exec_append_trans,
      apply int.of_nat (bcomp b false (↑((ccomp c1).length) + 1)).length,
      {
        have h_bcomp : exec (bcomp (b) (false) (↑((ccomp c1).length) + 1)) (0, s, stk) (↑ ((bcomp (b) (false) (↑((ccomp c1).length) + 1)).length) + ite (false = bval b s) (↑((ccomp c1).length) + 1) 0 , s, stk) :=
        begin
          apply bcomp_correct,
          linarith,
        end,
        apply h_bcomp,
      },
      simp,
      {simp [hcond],},
      {
        simp,
        simp [hcond],
        have h_ccomp_jmp : exec (ccomp c1 ++ JMP ↑((ccomp c2).length) :: ccomp c2) (0, s, stk) (↑((ccomp c1).length) + (↑((ccomp c2).length) + 1), t, stk) := 
        begin
          apply exec_append_trans,
          apply int.of_nat ((ccomp c1).length),
          apply ih,
          simp,
          {
            simp,
            have h_jmp_c2 : exec (JMP ↑((ccomp c2).length) :: ccomp c2) (0, t, stk) (↑((ccomp c2).length) + 1, t, stk) :=
            begin
              apply rtc.star.single,
              simp [exec1, nth],
              simp [iexec],
              finish, 
            end,
            apply h_jmp_c2,
          },
          simp,
        end,
        apply h_ccomp_jmp,
      },
      simp,

  },
  case ite_false : b c1 c2 { -- DONE
    simp [ccomp],

    apply exec_append_trans,
    apply int.of_nat (bcomp b false (↑((ccomp c1).length) + 1)).length,
    {
      have h_bcomp : exec (bcomp (b) (false) (↑((ccomp c1).length) + 1)) (0, s, stk) (↑ ((bcomp (b) (false) (↑((ccomp c1).length) + 1)).length) + ite (false = bval b s) (↑((ccomp c1).length) + 1) 0 , s, stk) :=
      begin
        apply bcomp_correct,
        linarith,
      end,
      apply h_bcomp,  
    },
    simp,
    {
      simp [hcond],
      linarith,
    },
    {
      simp,
      simp [hcond],
      have h_ccomp_jmp : exec (ccomp c1 ++ JMP ↑((ccomp c2).length) :: ccomp c2) (↑((ccomp c1).length) + 1, s, stk) (↑((ccomp c1).length) + (↑((ccomp c2).length) + 1), t, stk) := 
      begin
        apply exec_appendL_if,
        simp,
        {
          simp,
          apply exec_cons_1,
          apply ih,
        },
        simp,
        finish,
      end,
      apply h_ccomp_jmp,
    },
    simp,
  },
  case while_true : b c s1 s2 s3{ --DONE
    let cc := ccomp c,
    let cb := bcomp b false (list.length cc + 1),
    let cw := ccomp(While b c),
    have h_cond : exec cw (0, s1, stk) (list.length cb, s1, stk) := 
      begin
        -- specialize ih_h_step stk,
        simp [cw, ccomp],
        simp [cb, cc],
        apply exec_appendR,
        have h_with_ite : exec (bcomp b false (↑((ccomp c).length) + 1)) (0, s1, stk)
          (↑((bcomp b false (↑((ccomp c).length) + 1)).length), s1, stk) =
          exec (bcomp b false (↑((ccomp c).length) + 1)) (0, s1, stk) 
          (↑((bcomp b false (↑((ccomp c).length) + 1)).length) + ite (false = bval b s1) (↑((ccomp c).length) + 1) 0, s1, stk) := 
          begin
            simp [hcond],
          end,
        rw [h_with_ite],
        apply bcomp_correct,
        have h_nneg : 0 ≤ ↑((ccomp c).length) :=
        begin
          simp [list.length_nneg],
        end,
        linarith,
      end,
    have h_do : exec cw (list.length cb, s1, stk) (list.length cb + list.length cc, s2, stk) := 
      begin
        specialize ih_h_step stk,
        simp [cw, ccomp],
        simp [cb, cc],
        have h_with_zero : exec
          (bcomp b false (↑((ccomp c).length) + 1) ++
            (ccomp c ++ [JMP (-1 + (-↑((ccomp c).length) + -↑((bcomp b false (↑((ccomp c).length) + 1)).length)))]))
          (↑((bcomp b false (↑((ccomp c).length) + 1)).length), s1, stk)
          (↑((bcomp b false (↑((ccomp c).length) + 1)).length) + ↑((ccomp c).length), s2, stk) =
          exec
          (bcomp b false (↑((ccomp c).length) + 1) ++
            (ccomp c ++ [JMP (-1 + (-↑((ccomp c).length) + -↑((bcomp b false (↑((ccomp c).length) + 1)).length)))]))
          (↑((bcomp b false (↑((ccomp c).length) + 1)).length) + 0, s1, stk)
          (↑((bcomp b false (↑((ccomp c).length) + 1)).length) + ↑((ccomp c).length), s2, stk) := by simp,
        rw [h_with_zero],
        clear h_with_zero,
        apply exec_appendL,
        apply int.of_nat((ccomp c).length),
        apply int.of_nat((ccomp c).length),
        apply exec_appendR,
        apply ih_h_step,
      end,
    have h_back : exec cw (list.length cb + list.length cc, s2, stk) (0, s2, stk) := 
      begin
        simp [cw, ccomp],
        simp [cb, cc],
        have h_with_zero :
          exec
          (bcomp b false (↑((ccomp c).length) + 1) ++
          (ccomp c ++ [JMP (-1 + (-↑((ccomp c).length) + -↑((bcomp b false (↑((ccomp c).length) + 1)).length)))]))
          (↑((bcomp b false (↑((ccomp c).length) + 1)).length) + ↑((ccomp c).length), s2, stk)
          (0, s2, stk) =
          exec
          (bcomp b false (↑((ccomp c).length) + 1) ++
          (ccomp c ++ [JMP (-1 + (-↑((ccomp c).length) + -↑((bcomp b false (↑((ccomp c).length) + 1)).length)))]))
          (↑((bcomp b false (↑((ccomp c).length) + 1)).length) + ↑((ccomp c).length), s2, stk)
          (↑((bcomp b false (↑((ccomp c).length) + 1)).length) + (↑((ccomp c).length) -↑((bcomp b false (↑((ccomp c).length) + 1)).length) - ↑((ccomp c).length)), s2, stk) := by simp,
        rw [h_with_zero],
        clear h_with_zero,
        apply exec_appendL,
        apply int.of_nat((ccomp c).length),
        apply int.of_nat((ccomp c).length),
        have h_with_zero_2 :
          exec
          (ccomp c ++ [JMP (-1 + (-↑((ccomp c).length) + -↑((bcomp b false (↑((ccomp c).length) + 1)).length)))])
          (↑((ccomp c).length), s2, stk)
          (↑((ccomp c).length) - ↑((bcomp b false (↑((ccomp c).length) + 1)).length) - ↑((ccomp c).length), s2, stk) =
         exec
          (ccomp c ++ [JMP (-1 + (-↑((ccomp c).length) + -↑((bcomp b false (↑((ccomp c).length) + 1)).length)))])
          (↑((ccomp c).length) + 0, s2, stk)
          (↑((ccomp c).length)  + ( -↑((bcomp b false (↑((ccomp c).length) + 1)).length)  + -↑((ccomp c).length)), s2, stk) := by simp,
        rw [h_with_zero_2],
        clear h_with_zero_2,
        apply exec_appendL,
        apply int.of_nat(list.length ([JMP])),
        apply int.of_nat(list.length ([JMP])),
        apply rtc.star.single,
        simp [exec1, nth],
        simp [iexec],
        finish,
      end,
    have h_out : exec cw (0, s2, stk) (list.length cw, s3, stk) := 
      begin
        specialize ih_h_step_1 stk,
        simp [cw],
        apply ih_h_step_1,
      end,

    show exec cw (0,s1,stk) (list.length cw, s3, stk),
    apply rtc.star.trans,
    apply h_cond,
    {
      apply rtc.star.trans,
      apply h_do,
      {
        apply rtc.star.trans,
        apply h_back,
        apply h_out,
      }
    },
  },
  case while_false : b c{ --DONE
    let cc := ccomp c,
    let cb := bcomp b false (list.length cc + 1),
    let cw := ccomp(While b c),
    simp [ccomp],
    apply exec_append_trans,
    apply int.of_nat (cb.length),
    {
        have h_bcomp : exec (bcomp b (false) (↑((ccomp c).length) + 1)) (0, t, stk) (↑ ((bcomp (b) (false) (↑((ccomp c).length) + 1)).length) + ite (false = bval b t) (↑((ccomp c).length) + 1) 0 , t, stk) :=
        begin
          apply bcomp_correct,
          linarith,
        end,
        apply h_bcomp, 
    },
    {
      simp [hcond],
      linarith,
    },
    {
      simp,
      simp [hcond],
      have h_ccomp_jmp : exec (ccomp c ++ [JMP (-1 + (-↑((ccomp c).length) + -↑((bcomp b false (↑((ccomp c).length) + 1)).length)))])
        (↑((ccomp c).length) + 1, t, stk)
        (↑((ccomp c).length) + 1, t, stk) := 
        begin apply rtc.star.refl, end,
      apply h_ccomp_jmp,
    },
    simp,
  },
end



end LoComp
