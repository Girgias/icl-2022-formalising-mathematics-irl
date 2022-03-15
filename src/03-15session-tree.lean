import combinatorics.simple_graph.connectivity

#check simple_graph.walk.take_until

/-!
# Trees!

A graph is a tree if for every pair of vertices there is a unique
path between them

Things to try:

1) tree ↔ ∃! trails
2) tree ↔ connected + no cycles

-/


universe u₀

namespace simple_graph

def is_tree {V : Type u₀} (G : simple_graph V) : Prop :=
∀ u v : V, ∃! p : G.walk u v, p.is_path

def is_connected {V : Type u₀} (G : simple_graph V) : Prop :=
∀ u v : V, ∃ p : G.walk u v, p.is_path

namespace is_tree
variables {V: Type u₀} { G : simple_graph V} 

lemma is_tree.is_connceted {V : Type u₀} (G : simple_graph V)
  (h: G.is_tree) : G.is_connected :=
begin
  intros u v,
  exact exists_unique.exists (h u v),
end

open simple_graph.walk

example (X : Type) (P: X → Prop) (hP : ∃! a : X, P a) (x y : X)
  (hx : P x) (hy : P y) : x = y := exists_unique.unique hP hx hy

lemma no_cycles [decidable_eq V] (hG: G.is_tree) (u : V) (p: G.walk u u) (hp : p.is_cycle)
 : false :=
begin
  cases p with _ _ v _ huv q,
  -- Nil walk is not a cycle
  {
    exact hp.ne_nil rfl,
  }, {
    set w1 := walk.cons huv nil with hw1,
    set w2 := q.reverse with hw2,
    have hw1path : w1.is_path,
    {
      simp,
      intro h,
      rewrite h at huv,
      exact G.loopless v huv,
    },
    have hw2path : w2.is_path,
    { sorry },

    have hw := exists_unique.unique (hG u v) hw1path hw2path,
    sorry,
    -- stopping because no time
  },
end

variables {u v w : V} (p : G.walk u v)


end is_tree
end simple_graph
