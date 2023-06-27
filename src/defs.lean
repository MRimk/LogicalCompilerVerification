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


/- # Definitions -/
def vname := string

def val := ℤ

def stack := list ℤ 

/- 
  ## Reflexive Transitive Closure - Star

  adapted from https://lean-forward.github.io/logical-verification/2021/ course
-/
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

/- 
  ## State: variable name → ℤ 

  adapted from https://lean-forward.github.io/logical-verification/2021/ course
-/

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


/- ## Instruction -/

inductive instr : Type
| LOADI : ℤ → instr
| LOAD : vname → instr 
| ADD : instr
| SUB : instr
| MUL : instr
| DIV : instr
| STORE : vname → instr
| JMP : int → instr
| JMPLESS : int → instr
| JMPGE : int → instr
| NOP : instr


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
  ## Single step execution
  Execute one instruction
  check if pc is in a valid location in the list 
-/
def exec1  (li : list instr) (c : config)  (c' : config) : Prop := 
( c' = iexec (nth li c.fst) c ∧ 0 ≤ c.fst ∧ c.fst < li.length)  

/-
  ## Intro rule
-/
lemma exec1I {li : list instr} {i s stk c'}
  (h_eq: c' = iexec (nth li i) (i, s, stk))
  (h_nneg : 0 ≤ i) 
  (h_less : i < li.length):
  exec1 li (i, s, stk) c' := 
  begin 
    simp [exec1],
    simp [h_eq, h_nneg, h_less],
  end

/- ## Multiple step execution -/
abbreviation exec (li : list instr) (c : config) (c' : config) : Prop :=
star (exec1 li) c c'

end LoComp