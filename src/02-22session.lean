import tactic
import topology.basic

/-!
Starting with a theorem
If f: X → Y is a function then the folowing are equivalent:
1) f is surjective;
2) ∃ g : Y → X such that "g is a one-sided inverse of f" i.e. ∀ y ∈ Y, f(g(y)) = y
  i.e. f∘g = id_y

The proof:
1 ⇒ 2:
  Define g thus if y ∈ Y, by surjectivity of f ⇒ ∃ x ∈ X s.t. f(x) = y
  Define g(y) to be this x. ∎

2 ⇒ 1
  If y ∈ Y need x ∈ X such that f(x) = y.
  But x = g(y) works. ∎


Surjectivity of f means {x ∈ X | f(x) = y} ≠ ∅
This proof uses axiom of choice

Try proving this in Lean.
-/

variables (X Y : Type) (f : X → Y)

example (f g: X → Y) (h: f = g) : ∀ x, f x = g x :=
begin
  intro x,
  exact congr_fun h x,
end

example : function.surjective f ↔
  ∃ g : Y → X, f ∘ g = id :=
begin
  split, {
    intro h,
    -- Nonsense
    --have h37 : f = f, refl,
    let g_not_working : Y → X, {
      -- Lean has two universes Type and Prop
      -- examples of types ℝ, ℕ, G (a group)
      -- examples of Prop "2+2=4", "2+2=5", Fer;at last Theorem
      -- examples of terms π, 7, 9 or proofs of 2+2=4
      -- but everything is a term which has type of the "above layer"
      -- Prop is a term of Type, and Type is a term of Type 1, which is a term of Type2, etc.
      -- Note Type is identical to Type0
      -- And Prop = Sort0, Type = Sort1, Type1 = Sort2, etc.
      intro y,
      unfold function.surjective at h,
      specialize h y,
      -- Try to use axiom of choice
      -- how to get a from h,
      -- "cases h with x hx" does not work as we shouldn't be creating data in tactic mode
      -- see below
      -- the fix is to not do this
      sorry,
    },
    -- need an axiom of choice tactic
    choose g hg using h,
    use g,
    -- extentionality tactic for functions
    ext y,
    exact hg y,
  }, {
    intro h,
    cases h with g hg,
    replace hg := congr_fun hg,
    change ∀ y, f (g y) = y at hg,
    intro y,
    use g y,
    apply hg,
    -- Golfed version
    -- rintro ⟨g, hg⟩ y,
    -- exact ⟨g y, (congr_fun hg) y⟩,
  } 
end

#check Y → X
#check f

#check Exists
#check @Exists.rec
#check @nat.rec

example (a : ℕ) : ℕ :=
begin
  cases a,
  sorry, sorry,
end
-- bad case because of recursive
example (h : ∃ x : ℕ, x = x) : ℕ :=
begin
  cases h,
  sorry,
end

/-
  In Lean the axiom of choice is your route from Prop to Type
  Proofs are not stored.

  Axiom of choice in Lean is a function (∃ x: X, px) → X
-/

#check nonempty
#check @classical.choice

-- Need to write non computable as we're using axiom of choice
noncomputable def foo : ℕ :=
begin
  have h : nonempty ℕ,
    { exact ⟨2⟩ },
  exact classical.choice h,
end

/-!
# Second hour
-/
class has_star (α : Type) :=
{ starry_element : α }

notation `★` := has_star.starry_element

instance : has_star ℕ :=
{ starry_element := 37 }

#eval 30 + ★

instance : has_star ℤ :=
{ starry_element := 42 }

#eval (30 : ℤ) + ★

class my_group (G: Type) extends has_mul G, has_one G, has_inv G :=
( mul_assoc : ∀ g h k : G, g * (h * k) = (g * h) * k)
-- Has error, because Lean doesn't know what is meant by 1
-- One fix is to add has_one to the extends
( one_mul : ∀ g : G, 1 * g = g)
-- Or use
-- ( one_mul : ∃ e : G, ∀ g : G, e * g = g)
-- But then how do we "get" the identity, so use initial thing
( inv_mul : ∀ g, g * g⁻¹ = (1 : G))

structure my_group_iso (G H : Type)
 [group G] [group H] :=
 (f : G → H)
 (hmul : ∀ a b : G, f(a * b) = f a * f b)
 (hbij : function.bijective f)

example (G H : Type) [group G] [group H] (e : my_group_iso G H): G :=
 -- hard to access the inverse function
begin
  sorry,
end


structure my_homeomorphism (X Y : Type)
  [topological_space X] [topological_space Y] :=
  (f : X → Y)
  --(hf : function.bijective f) -- terrible idea
  -- Just carry the inverse around by adding it to the structure
  (g : Y → X)
  (h_cont : continuous f)
  (h_cont_inv : continuous g)
  (h1 : f ∘ g = id)
  (h2 : g ∘ f = id)

#check equiv
#check equiv ℕ ℕ

example : ℕ ≃ ℕ :=
{
  to_fun := λ x, x,
  inv_fun := λ y, y,
  left_inv := begin intro x, dsimp only, refl, end,
  right_inv := begin intro y, refl, end,
}

example (P: Prop) (h1 : P) (h2 : P) : h1 = h2 :=
begin
  refl,
end

def e1 : ℤ ≃ ℤ :=
{
  to_fun := id,
  inv_fun := id,
  left_inv := λ x, rfl,
  right_inv := λ y, rfl,
}
def e2 : ℤ ≃ ℤ :=
{
  to_fun := λ x, -x,
  inv_fun := λ y, -y,
  left_inv := λ x, begin dsimp only, ring, end,
  right_inv := λ y, begin dsimp, ring, end,
}

example (X Y : Type) (e : X ≃ Y) : Y ≃ X :=
--equiv.symm e
-- or
e.symm


def foobar (X Y : Type) (e : X ≃ Y) : X → Y := e
#print foobar
-- coercion is happening

example (X Y : Type) (e : X ≃ Y) : Y → X := e.symm

example (Z : Type) (e : X ≃ Y) (f : Y ≃ Z): X ≃ Z  := e.trans f

/-!
# Some tricks
-/

-- Get gols for all ands
example (P Q : Prop) : P ∧ Q ∧ P ∧ P :=
begin
  refine ⟨_, _, _, _⟩,
  sorry, sorry, sorry, sorry,
end