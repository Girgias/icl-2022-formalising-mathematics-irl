import tactic
import topology.continuous_function.compact

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

-- Let X and Y be topologycal spaces
variables (X Y : Type) [topological_space X] [topological_space Y]
variable (S : set X)

-- goal : f : X → Y and C ⊂ X compact implies f(C) compact

#check is_open S
#check is_compact S
#check is_closed S

variables (f : X → Y) (h : continuous f)

#check f '' S
-- `''` does something to handle set terms for types
example (hf : continuous f) : is_compact S → is_compact(f '' S) :=
begin
  intro h,
  /-
    What's the maths proof?
    Let Uᵢ : i ∈ I be an open cover of f(S)
    Let Vᵢ be a preimage of Uᵢ
    Vᵢ all open because f is continous
    S ⊆ union of the Vᵢ
    compactness implies finite subcover V₁, V₂, ..., Vₙ
    then U₁, U₂, ..., Uₙ work
  -/
  rw is_compact_iff_finite_subcover at *,
  -- finset is term of finite set
  -- Let Uᵢ : i ∈ I be an open cover of f(S)
  intros I U hU h,
  -- Let Vᵢ be a preimage of Uᵢ
  set V : I → set X := λ i, f⁻¹' (U i) with hV,
  have hVopen : ∀ i, is_open (V i),
  {
    intro i,
    rw hV,
    dsimp,
    apply continuous.is_open_preimage hf,
    apply hU,
  },
  -- S ⊆ union of the Vᵢ
  -- Needs to stop because time
  sorry,
end




