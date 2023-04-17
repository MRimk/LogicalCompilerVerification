import .love08_operational_semantics_demo .love01_definitions_and_statements_demo


/-! # LoVe Demo 8: Operational Semantics

In this and the next two lectures, we will see how to use Lean to specify the
syntax and semantics of programming languages and to reason about the
semantics. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

-- namespace LoVe
namespace LoComp

open LoVe

def vname := string

def val := ℤ

def stack := list ℤ -- TODO: ???val??? how do we make it accept 

def state := vname → val


inductive instr : Type  -- page 35 
| LOADI : val → instr
| LOAD : vname → instr 
| ADD : instr
| SUB : instr
| MUL : instr
| DIV : instr


open instr

def execl : instr → state → stack → stack 
| (LOADI n) _ stk := n :: stk
| (LOAD x) s stk :=  (s x) :: stk 
| ADD _ (j :: i :: stk ) := (i + j) :: stk
| ADD _ nil := nil  -- anything where it cannot compute
| SUB _ (j :: i :: stk ) := (i - j) :: stk
| SUB _ nil := nil
| MUL _ (j :: i :: stk ) := (i * j) :: stk
| MUL _ nil := nil
| DIV _ (j :: i :: stk ) := (i / j) :: stk
| DIV _ nil := nil




def exec : list instr → state → stack → stack
| list.nil _ stk := stk
| (i :: is) s stk := exec is s (execl i s stk)


open LoVe.aexp

def comp : aexp → list instr
| (num n) := [LOADI n]
| (var x) := [LOAD x]
| (aexp.add a b) := comp a ++ comp b ++ [ADD] 
| (aexp.sub a b) := comp a ++ comp b ++ [SUB] 
| (aexp.mul a b) := comp a ++ comp b ++ [MUL] 
| (aexp.div a b) := comp a ++ comp b ++ [DIV] 




lemma exec_comp_eq_eval {x : aexp}  {s stk} :
  exec (comp x) s stk = (eval s x) :: stk :=
begin
  induction' x,
  case LoVe.aexp.num {
    simp [comp, exec],
    refl,
  },
  case LoVe.aexp.var {
    simp [comp, exec],
    refl,
  },
  case LoVe.aexp.add {
    simp [comp, exec, ih_x, ih_x_1, eval, add_comm, add_assoc],
    sorry,
  },
  case LoVe.aexp.sub {
    simp [comp, exec],
    sorry,
  },
  case LoVe.aexp.mul {
    simp [comp, exec],
    sorry,
  },
  case LoVe.aexp.div {
    simp [comp, exec, ih_x, ih_x_1, eval],
    sorry,
  },
end




end LoComp
