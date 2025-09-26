import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
section
  universe u v
  @[simp] lemma array_map_getElem! {α : Type u} {β : Type v}
      [Inhabited α] [Inhabited β]
      (a : Array α) (f : α → β) (k : Nat) (hk : k < a.size) :
      (a.map f)[k]! = f (a[k]!) := by
    classical
    simpa [Array.get!, Array.get?, hk]
end
-- </vc-helpers>

-- <vc-definitions>
def replace (v : Array Int) (x : Int) (y : Int) : Array Int :=
v.map (fun z => if z = x then y else z)
-- </vc-definitions>

-- <vc-theorems>
theorem replace_spec (v : Array Int) (x y : Int) :
let v' := replace v x y
∀ k, 0 ≤ k ∧ k < v.size →
((v[k]! = x → v'[k]! = y) ∧
(v[k]! ≠ x → v'[k]! = v[k]!)) :=
by
  intro v'
  intro k hk
  constructor
  · intro hkx
    classical
    have h := array_map_getElem! v (fun z => if z = x then y else z) k hk.2
    simpa [v', replace, hkx] using h
  · intro hkne
    classical
    have h := array_map_getElem! v (fun z => if z = x then y else z) k hk.2
    have h' : v'[k]! = (if v[k]! = x then y else v[k]!) := by
      simpa [v', replace] using h
    simpa [hkne] using h'
-- </vc-theorems>
