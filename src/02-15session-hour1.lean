import tactic
import data.nat.prime
import topology.continuous_function.compact

/-!

∀
∀ x : ℕ, x = 37
-/

#check ∀ x : ℕ, x = 37

lemma easy : 2 + 2 = 4 :=
begin
  norm_num,
end

#check 2 + 2 = 4
#check easy

/-!
# Infinte unions

Want to do ⋃ A₁, A₂, ... are all sets
and i is a natural
-/

variable (X : Type)
variables (U V : set X)

#check U 
#check U ∪ V
#print notation ∪
#print notation ⋃

variable (A : ℕ → set X)

#check A(0)
 -- want to take union of all the A(i)
#check ⋃ (i : ℕ), A i

variable (B : ℕ → ℕ → set X)

-- set_option pp.notation false (to disable unicode notation)
#check ⋃ (i : ℕ), ⋃ (j : ℕ), B i j
#check ⋃ (i : ℕ) (j : ℕ), B i j
#check ⋃ (i j : ℕ), B i j

#check nat.prime
#check nat.prime 6

def primes : Type := {n : ℕ // nat.prime n} -- // creates a dependent pair
def primes_set : set ℕ  := {n : ℕ | nat.prime n}

variables (x : primes)
#check x.1
#check x.2

def two : primes := ⟨2, begin
  exact nat.prime_two,
end⟩

example : 2 ∈ primes_set :=
begin
  unfold primes_set,
  dsimp, -- definition simplification
  exact nat.prime_two,
end

#check ⋃ (p: primes), A (p.1)
#check ⋃ (p ∈ primes_set), A p --- exciting new development
-- ⋃ (p ∈ S), ... works!

#check set.mem_bUnion

example (a : X) : a ∈ (⋃(i : ℕ), A i) ↔ ∃ j, a ∈ A j :=
begin
  exact set.mem_Union, -- key fact for unions
end

example (a : X) : a ∈ (⋃ (p ∈ primes_set), A p) ↔ ∃ p : ℕ, nat.prime p ∧ a ∈ A p :=
begin
  rw set.mem_Union,
  simp_rw set.mem_Union,
  split,
    --intro h,
    --cases h with i hi,
    --cases hi with h1 h2,
    --use i,
    --split,
    --  exact h1, exact h2,
    { 
      rintro ⟨i, h1, h2⟩,
      exact ⟨i, h1, h2⟩
    },
--  unfold primes_set,
  {sorry}
end




/-!
## Second hour
Things to know

Well I'm now rep for the class

OpenAI have been in touch with Buzzard, and want to give money
for people who formalise olympid questions on the Xena dicord

Check on Twitter of OpenAI for link to blog

And Meta (Facebook) want our emai;l address to have a meeting where they show off
their extension for VSCode to guess the next line of a Lean 

PDF where fine for the project

Can Buzzard share the projects for:
- next year students
- to the world


And NOW
## Topology
check the sheets of the formalising course (section 7)

 -/

-- Let X be a topologycal space
variables (Z : Type) [topological_space X]






