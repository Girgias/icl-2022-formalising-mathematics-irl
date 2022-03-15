
import tactic
/-!

# About Quotients

There are two ways to define new objets in maths:
 - The first way is tosay what they are
 - The second way is to say what they do

Example 1 the natural numbers ℕ 
Definition via "what they are"
  0 = ∅ 
  1 = {0}
  2 = {0, 1}
  3 = {0, 1, 2}
  [...] 

Theorem is that induction works

Def in Lean:
Inductive nat
| zero : nat
| succ :  nat -> nat

0 is a natural
the succesor of a natural is a natural
*done*
to do something for all n ∈ ℕ suffices to:
 * do it for 0
 * if done for n can do for succ n

-/

 #check ℕ
 #print ℕ

 /-!
 ## Product

 if X, Y are sets (or types)
 X ⨯ Y is a set (type)
 (x, y) where x ∈ X, y ∈ Y
 which is not equal to {x, y} because order matters

 So what is this 


 FACT
 (x₁, y₁) = (x₂, y₂) ↔ x₁ = x₂ ∧ y₁ = y₂

 ## Quotients

 Lets do Tensor products
 If V and W are vector spaces over ℝ then there exist another vector space V ⊕⨯ W
 ∃ linear map 

## Actually Quotients

Set-up: X is a set/type
~ : equivalence relation on X 
i.e. if a,b ∈ X a ~ b is a proposition
and it is reflecive symetric and transitive


2500 y ago
Euclid lists axio;s he'll use:
 and says that equality is an equivalence relation 
 
 e.g. colours of shapes is an eq
 e.g. take property that you care from the object and that all of these need to be equal


 f : X → Y, define a relation ~ on X by a ~ b ↔ f(a) = f(b)
 THM: that's an eq relation

Converse:
Say X is a thing and ~ is an equivalence relation on X
Q: Can I get a Y and f : X → Y such that x₁ ~ x₂ ↔ f(x₁) = f(x₂)

A: Yes! [x]~ = Y the set of equivalence classes 


ℤ/12ℤ is a set of sets of equivalence relations 
= {{-12, 0, 12, ...}, { -11, 1, 11, ...}, ...}

The lie X set ~ equiv relation then the quotient X/~ (called Y earlier) ***is*** the set of equivalence classes.

Another example
X = set of red & yellow & green & blue plastic shapes
~ is "same colour"

What I want : Y & f : X → Y s.t. a ~b ↔ f(a) = f(b)
"UG model"
  Y = {{a red triangle, a red square}, {2 blue triangles, blue pentagone},  ...}

Another model is:
Y = {red, yellox, green, blue}, f = "colour"

  We care about what they do and not what they are


  ### Quotients in Lean
  You can't ask what they are, only ask what they **do**
  
 -/

-- Let X be a type
variable (X : Type)
#check @quotient X

#check setoid

#check equivalence

-- Let R be an equivalence relation on X
variables (R : X → (X → Prop)) (h : equivalence R)

def s : setoid X := { r := R,
  iseqv := h }

  -- how does Lean make the set Y such that f:X→Y is a surjection
  -- and f(x₁) = f(x₂) ↔ R(x₁,x₂)

  def Y := @quotient X (s X R h)

  #check Y X R h

-- Let's do a concrete example
--- equiavalence relation on the integeres
-- type by \ then | = ∣ 
def C (a b : ℤ) : Prop := 12 ∣ (a - b)

lemma C_is_equiv : equivalence C :=
begin
  split,
  {sorry},
  {split, {sorry}, {sorry}}
end


--instance t : setoid ℤ := { r := C,
def t : setoid ℤ := { r := C,
  iseqv := C_is_equiv }
attribute [instance] t

def clock := quotient t 

  -- we don't know what it is
  -- It is "the quotient of the integers by the equivalence realation C"
    -- Does it do what it is supposed to do????

#check quotient.mk

def f : ℤ → clock := quotient.mk

example (a : ℤ) : f a = ⟦a⟧ :=
begin
  refl,
end

example (a b : ℤ) : C a b ↔ a ≈ b :=
begin
  refl,
end

example : f 1 = f 13 :=
begin
  -- quotient.sound says a ~ b → f a = f b
  --let h := quotient.sound,
  apply quotient.sound,
  change C 1 13,
  change (12 : ℤ) ∣ 1 - 13,
  norm_num,
end

#check quotient.eq

example (a b : ℤ) : ⟦a⟧ = ⟦b⟧ ↔ a ≈ b :=
begin
  exact quotient.eq,
end

-- surjective_quot_mk from the mathlib

-- What does it mean to be "well-defined"
-- For nagation we need
-- a ~ b ⇒ -a ~ -b 

/-!
For ℤ/12 → X

Fact to give g : ℤ/12ℤ → X
need two ingredients
1: g⁀ : ℤ → X 
2: proof that a ~ b then g⁀(a) = g⁀(b)
-/

example (Z : Type) (gtilde : ℤ → Z)
  (h : ∀ a b : ℤ, a ≈ b → gtilde a = gtilde b)
  : clock → Z :=
  quotient.lift gtilde h


