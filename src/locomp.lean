import .love08_operational_semantics_demo .love01_definitions_and_statements_demo


-- set_option pp.beta true
-- set_option pp.generalized_field_notation false

namespace LoComp

open LoVe

def vname := string

def val := ℤ

def stack := list ℤ -- TODO: ???val??? how do we make it accept, because +, -, *, / is not defined for val

def state := vname → ℤ

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


open instr



def iexec : instr → config → config -- TODO: fill in the full matching
| (LOADI n) (i, s, stk) := (i + 1, s, n :: stk)
| (LOAD v) (i, s, stk) := (i + 1, s, s v :: stk)
| ADD (i, s, stk) := (i + 1, s, (head2 stk + stk.head) :: tail2 stk)
| SUB (i, s, stk) := (i + 1, s, (head2 stk - stk.head) :: tail2 stk)
| MUL (i, s, stk) := (i + 1, s, (head2 stk * stk.head) :: tail2 stk)
| DIV (i, s, stk) := (i + 1, s, (head2 stk / stk.head) :: tail2 stk)
| (STORE v) (i, s, stk) := (i + 1, s{v ↦ (stk.head)}, stk.tail) -- so state.update only works on the state that is not the correct one 
| (JMP n) (i, s, stk) := (i + 1 + n, s, stk)
| (JMPLESS n) (i, s, stk) := 
  if (head2 stk) < (stk.head)
  then (i + 1 + n, s, tail2 stk)
  else (i + 1, s, tail2 stk)
| (JMPGE n) (i, s, stk) := 
  if (head2 stk) ≥ (stk.head)
  then (i + 1 + n, s, tail2 stk)
  else (i + 1, s, tail2 stk)

/- redefinition for ints rather than nat -/ 
def nth : list instr → ℤ → option instr  
| (a :: l) 0 := option.some a
| (a :: l) n := nth l (n - 1)
| list.nil n := option.none


/- 
  Execute one instruction
  check if pc is in a valid location in the list 
-/
def exec1  (li : list instr) (c : config)  (c' : config) : Prop := -- TODO: fix option/instr
∃ i s stk, c = (i, s, stk) ∧ c' = iexec (nth li i) (i, s, stk) ∧ 0 ≤ i ∧ i < li.length  

/-
lemma exec1I [intro, code_pred_intro]:
  "c' = iexec (P!!i) (i,s,stk) ⟹ 0 ≤ i ⟹ i < size P
  ⟹ P ⊢ (i,s,stk) → c'"
by (simp add: exec1_def)
-/


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



end LoComp
