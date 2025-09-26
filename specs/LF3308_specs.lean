-- <vc-preamble>
def liquidDensity (l: Liquid) : Float :=
  match l with
  | Liquid.H => 1.36
  | Liquid.W => 1.0
  | Liquid.A => 0.87
  | Liquid.O => 0.8
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def separate_liquids (glass: List (List Liquid)) : List (List Liquid) := sorry

theorem count_preserving (glass: List (List Liquid)) : 
  let input_counts := ((glass.join.filter (fun x => x == Liquid.H)).length,
                      (glass.join.filter (fun x => x == Liquid.W)).length,
                      (glass.join.filter (fun x => x == Liquid.A)).length,
                      (glass.join.filter (fun x => x == Liquid.O)).length);
  let output := separate_liquids glass;
  let output_counts := ((output.join.filter (fun x => x == Liquid.H)).length,
                       (output.join.filter (fun x => x == Liquid.W)).length,
                       (output.join.filter (fun x => x == Liquid.A)).length, 
                       (output.join.filter (fun x => x == Liquid.O)).length);
  input_counts = output_counts := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem density_layering (glass: List (List Liquid)) :
  let result := separate_liquids glass
  ∀ i j, i < j → j < result.length →
  ∀ k, k < (result.get! i).length →
  liquidDensity ((result.get! i).get! k) ≤ liquidDensity ((result.get! j).get! k) := sorry

theorem empty_glass :
  separate_liquids [] = [] := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval separate_liquids [["H", "H", "W", "O"], ["W", "W", "O", "W"], ["H", "H", "O", "O"]]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval separate_liquids [["A", "H", "W", "O"]]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval separate_liquids []
-- </vc-theorems>