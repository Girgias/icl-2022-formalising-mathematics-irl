
import tactic
/-!
Plan for today
- inductive types
- the problem with the course
- trees
-/

inductive mynat : Type -- no :=
| zero : mynat
| succ : mynat → mynat

-- This is Peano's definition of ℕ
-- but if look on Wikipedia you see

#print mynat
#print mynat.zero
#print mynat.succ
#print mynat.rec --automatically made by Lean
--- The principle of induction and recursion

-- how to prove (1) succ is injective and 92) succ n ≠ zero ?

-- prove them by making more defintions
namespace mynat
-- we have our zero inside out namespace
#check zero

def is_zero : mynat → Prop
| zero := true
| (succ n) := false

lemma zero_is_zero : is_zero zero :=
begin
  change true,
  trivial,
end

lemma succ_ne_zero (n : mynat) : ¬ (is_zero (succ n)) :=
begin
  change ¬ false,
  exact id,
end

lemma zero_ne_succ (n : mynat) : succ n ≠ zero :=
begin
  intro h,
  apply succ_ne_zero,
  rw h,
  apply zero_is_zero,
end

def add : mynat → mynat → mynat
| n zero := n
| n (succ m) := succ (add n m)

instance : has_add mynat :=
{ add := add }

lemma add_zero (n : mynat) : n + zero = n :=
begin
  refl,
end

-- injectivity of succ
-- one way of doing it is to write a one sided inverse
-- f: X → Y so if ∃ g: Y → X such that ∀ x, g(f(x)) = x
-- f is the successor function which goes from ℕ to ℕ

def pred : mynat → mynat -- no :=
| zero := succ(succ(succ(succ(succ(zero)))))--anywhere is fine
| (succ n) := n

lemma pred_succ (n : mynat) : pred (succ n) = n :=
begin
  -- how to prove this?
  refl, --does the trick
end

-- there is a way to switch off dot notation but Kevin doesn't remember
lemma succ_inj : function.injective succ :=
begin
  intros a b h,
  apply_fun pred at h,
  -- same as but apply_fun is easier to remember (probably)
  --replace h := congr_arg pred h,
  simpa [pred_succ] using h,
end

end mynat

inductive mylist (X : Type) : Type
| nil : mylist -- empty list
| cons (x : X) (l : mylist) : mylist -- put x at the beginning

namespace mylist 
variables (a b c : ℕ)

-- list [a,b,c] of naturals
example : mylist ℕ := cons a (cons b (cons c nil))

variable {X : Type} -- make X implicit

-- joining lists together
def add : mylist X → mylist X → mylist X
| nil l := l
| (cons x m) l := cons x (add m l)

def singleton (x : X) : mylist X := cons x nil

def reverse : mylist X → mylist X
| nil := nil
| (cons x m) := add (reverse m) (singleton x)


-- Here is a surprisingly difficult question
theorem tricky (l : mylist X) : reverse (reverse l) = l :=
begin
  sorry,
end

end mylist

/-!
Now lets talk about graphs

*staring at mathlib/combinatorics/simple_graph/connectivity.lean file*
explaining what walk, trail, path, and cycles are in simple graphs

is_tree is a property of the graph and not of a walk
a tree is a graph which is connected but does not have a cycle

Tree: ∀ u, v ∈ V, ∃! p : path u v
Then theorem: no cycles


Problem new defs in mathlib in febuary but we have a version from Jan
So best create a new repo to do the graph theory stuff

Or one can do ``leanproject up`` in terminal to update mathlib.
-/

/-
THIRD ORALS sketch

Hand in deadline is 1PM Friday 1st for April

Proposal: we have a "conference" 2 PM to 3:30PM you all give 3 minute talks
on the 1st of April

where you share your screen and your code and say something about it
and convince Kevin we understand our code

No questions

Hybrid, people can be online or in person
-/
