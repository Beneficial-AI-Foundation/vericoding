-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def how_much_water (water : Float) (clothes load : Nat) : Float ⊕ String := sorry

def isGreaterThan (a b : Float ⊕ String) : Prop :=
  match a, b with
  | Sum.inl x, Sum.inl y => x > y
  | _, _ => False
-- </vc-definitions>

-- <vc-theorems>
theorem water_calculation_properties
  (water : Float) (clothes load : Nat)
  (h1 : water > 0)
  (h2 : water ≤ 1000)
  (h3 : clothes > 0)
  (h4 : clothes ≤ 100)
  (h5 : load ≤ 200) :
  let result := how_much_water water clothes load
  (load > 2 * clothes → result = Sum.inr "Too much clothes") ∧
  (load < clothes → result = Sum.inr "Not enough clothes") ∧
  (clothes ≤ load ∧ load ≤ 2 * clothes →
    match result with
    | Sum.inl x => x ≥ 0 ∧ isGreaterThan (how_much_water (2 * water) clothes load) result
    | Sum.inr _ => False) := sorry

theorem increasing_load_increases_water
  (water : Float) (clothes load : Nat)
  (h1 : water ≥ 0.1)
  (h2 : water ≤ 100)
  (h3 : clothes > 0)
  (h4 : clothes ≤ 20)
  (h5 : load = clothes)
  (h6 : load + 1 ≤ 2 * clothes) :
  isGreaterThan (how_much_water water clothes (load + 1)) (how_much_water water clothes load) := sorry

theorem known_value_test :
  how_much_water 50 15 29 = Sum.inl 189.87 := sorry
-- </vc-theorems>