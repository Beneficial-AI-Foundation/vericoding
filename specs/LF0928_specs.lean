-- <vc-preamble>
def list_max (xs : List Float) : Float :=
  match xs with
  | [] => 0
  | x::xs => xs.foldl max x

def list_min (xs : List Float) : Float :=
  match xs with
  | [] => 0
  | x::xs => xs.foldl min x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Point := Float × Float

def calc_expected_area (n: Nat) (vertices: List Point) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem area_is_non_negative {n: Nat} {vertices: List Point} :
  vertices.length = n → n ≥ 3 →
  calc_expected_area n vertices ≥ 0 :=
sorry

theorem area_smaller_than_bounding_box {n: Nat} {vertices: List Point} :
  vertices.length = n → n ≥ 3 →
  let xs := vertices.map (·.1)
  let ys := vertices.map (·.2)
  calc_expected_area n vertices ≤ (list_max xs - list_min xs) * (list_max ys - list_min ys) + 1e-10 :=
sorry

theorem area_invariant_under_translation {n: Nat} {vertices: List Point}
  {dx dy: Float} :
  vertices.length = n → n ≥ 3 →
  let translated := vertices.map (fun (x, y) => (x + dx, y + dy))
  (calc_expected_area n vertices - calc_expected_area n translated).abs < 1e-10 :=
sorry

theorem area_scales_quadratically {n: Nat} {vertices: List Point} :
  vertices.length = n → n ≥ 3 →
  let scaled := vertices.map (fun (x, y) => (2*x, 2*y))
  (calc_expected_area n scaled - 4 * calc_expected_area n vertices).abs < 1e-10 :=
sorry
-- </vc-theorems>