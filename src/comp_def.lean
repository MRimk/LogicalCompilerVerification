import .defs
import .exec

namespace LoComp

open instr

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
      cb1 := bcomp b1 false m
    in cb1 ++ cb2
| (Less a1 a2) f n := acomp a1 ++ acomp a2 ++ 
  (if (f = true) then [JMPLESS n] else [JMPGE n])

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



end LoComp