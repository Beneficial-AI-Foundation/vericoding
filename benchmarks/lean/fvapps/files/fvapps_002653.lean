-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def inverse_slice {α : Type} (list : List α) (s : Nat) (e : Nat) : List α :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem length_property {α : Type} (lst : List α) (a b : Nat) 
  (h1 : a ≤ b) (h2 : b ≤ lst.length) :
  (inverse_slice lst a b).length = lst.length - (b - a) :=
  sorry

theorem preserve_prefix {α : Type} (lst : List α) (a b : Nat)
  (h1 : a ≤ b) (h2 : b ≤ lst.length) :
  (inverse_slice lst a b).take a = lst.take a :=
  sorry

theorem preserve_suffix {α : Type} (lst : List α) (a b : Nat)
  (h1 : a ≤ b) (h2 : b ≤ lst.length) :
  (inverse_slice lst a b).drop a = lst.drop b :=
  sorry

theorem empty_slice {α : Type} (lst : List α) (i : Nat) (h : i ≤ lst.length) :
  inverse_slice lst i i = lst :=
  sorry

theorem remove_all {α : Type} (lst : List α) :
  inverse_slice lst 0 lst.length = [] :=
  sorry

theorem keep_all {α : Type} (lst : List α) :
  inverse_slice lst lst.length lst.length = lst :=
  sorry
-- </vc-theorems>