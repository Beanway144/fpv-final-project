namespace zfc
/------------------------------------__ZFC__------------------------------------/
/-The type Set and its member relation are introduced with no inherent meaning.-/
constant Set : Type
constant mem : Set → Set → Prop

  /- - - - Convenience Notations- - - -/
  infix ` ∈ ` : 90 := mem

  --We call `a` a subset of `A` if for every set `x ∈ a`, we have `x ∈ A`.
  def is_subset : Set → Set → Prop :=
    λ a A, (∀(x : Set), x ∈ a → x ∈ A)
  infix ` ⊂ ` : 90 := is_subset
  

/-----------------------------------Axioms---------------------------------------/
/-       Axioms based on Thomas Jech's set theory textbook, 1978, with          -/
/-    the exception that the empty set's existence is explicitly axiomatized.   -/

--__Axiom of Extensionality__
-- If sets `s` and `t` have the same elements, then `s = t`. 
axiom extensionality : ∀(s t x : Set), (x ∈ t ↔ x ∈ s) → s = t

--__Axiom of Pairing__
-- For any sets `a` and `b`, there exists a set `s` that contains exactly `a` and `b`.
axiom pairing : ∀(a b : Set), ∃(s : Set), ∀(e : Set), e ∈ s → e = a ∨ e = b

noncomputable def pair : Set → Set → Set :=
  λa b, classical.some (pairing a b)

--__Axiom Schema of Separation__
-- If `P` is some property, then for any set `s`, there exists
-- a set `t = {u ∈ s : P(u)}` that contains all those `u ∈ s` with property `P`.
axiom separation : ∀(P : Set → Prop) (s : Set), ∃(t : Set), ∀(u : Set),
  u ∈ t ↔ u ∈ s ∧ P u

--__Axiom of Empty Set__
-- There exists a set (called the empty set) such that no set is an element of it.
axiom empty_set : ∃(s : Set), ∀(x : Set), ¬(x ∈ s)

noncomputable def empty : Set := classical.some empty_set

 
--__Axiom of Union__
-- For any set `s`, there exists a set `t` containing exactly the elements of elements
-- of `s`.
axiom union : ∀(s : Set), ∃(t : Set), ∀(sel sel_el tel: Set), 
  sel ∈ s → sel_el ∈ sel → tel ∈ t ↔ sel_el = tel

noncomputable def union_of : Set → Set :=
  λ(s : Set), classical.some (union s)
prefix `∪` : 110 := union_of


--__Axiom of Power Set__
-- For any set `s` there exists a set `t` that contains exactly all the subsets of `s`
-- (called the power set of `s`).
axiom power_set : ∀(s : Set), ∃(t : Set), ∀(e : Set), e ∈ t ↔ e ⊂ s 

noncomputable def power_set_of : Set → Set := 
  λ(s : Set), classical.some (power_set s)
noncomputable def P := power_set_of

--__Axiom of Infinity__
-- There exists an inductive infinite set.
-- {`{}`, `{{}}`, `{{}, {{}}}`,...}
axiom infinity : ∃(inf : Set), empty ∈ inf ∧ (∀(s S: Set), s = ∪S → (s ∈ inf → S ∈ inf ))

--__Axiom Schema of Replacement__
-- For some function of sets `φ`, the image of `φ` is also a set.
axiom replacement : ∀(s: Set) (φ : Set → Set), (∀(x y a : Set), x ∈ s ∧ φ(x) = y → φ(x) = a ↔ a = y) →
  ∃(t : Set), ∀(z x: Set), x ∈ s → z ∈ t ↔ φ(x) = z

-- __Axiom of Regularity__
-- For any set nonempty set `s`, there exists a set `y` in `s` such that `s` and
-- `y` have no common elements. In other words, `s` has a ∈-minimal element.
axiom regularity : ∀(s : Set), ∃(x : Set), x ∈ s →
  ∃(y : Set), y ∈ s ∧ ¬(∃(z : Set), z ∈ y ∧ z ∈ s)

--__Axiom of Choice__
-- For any nonempty set X, there exists a ("choice") function from X that returns some element of X. 
axiom choice : ∀(s : Set), ¬(empty = s) → (∃(f : Set → Set),
  ∀(x : Set), x ∈ s ↔ f(x) ∈ x)
end zfc