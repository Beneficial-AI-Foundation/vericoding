-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def convert_to_dms (lat: String) (lon: String) : String × String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem coordinate_format_length 
  {lat: Float} {lon: Float} 
  (hlat: -90 ≤ lat ∧ lat ≤ 90) 
  (hlon: -180 ≤ lon ∧ lon ≤ 180) :
  let (lat_str, lon_str) := convert_to_dms (toString lat) (toString lon)
  String.length lat_str ≥ 14 ∧ 
  String.length lon_str ≥ 14 :=
sorry

theorem coordinate_format_direction
  {lat: Float} {lon: Float}
  (hlat: -90 ≤ lat ∧ lat ≤ 90)
  (hlon: -180 ≤ lon ∧ lon ≤ 180) :
  let (lat_str, lon_str) := convert_to_dms (toString lat) (toString lon)
  let pos : String.Pos := ⟨Nat.sub lat_str.length 1⟩
  let lat_last := lat_str.get? pos
  let lon_last := lon_str.get? pos
  (lat_last = some 'N' ∨ lat_last = some 'S') ∧
  (lon_last = some 'E' ∨ lon_last = some 'W') :=
sorry

theorem direction_consistency
  {lat: Float} {lon: Float}
  (hlat: -90 ≤ lat ∧ lat ≤ 90) 
  (hlon: -180 ≤ lon ∧ lon ≤ 180) :
  let (lat_str, lon_str) := convert_to_dms (toString lat) (toString lon)
  let pos : String.Pos := ⟨Nat.sub lat_str.length 1⟩
  let lat_last := lat_str.get? pos
  let lon_last := lon_str.get? pos
  (lat_last = some 'N' ↔ lat ≥ 0) ∧
  (lon_last = some 'E' ↔ lon ≥ 0) :=
sorry

theorem coordinate_parts_format
  {lat: Float} {lon: Float}
  (hlat: -90 ≤ lat ∧ lat ≤ 90)
  (hlon: -180 ≤ lon ∧ lon ≤ 180) :
  let (lat_str, lon_str) := convert_to_dms (toString lat) (toString lon)
  let lat_parts := (lat_str.dropRight 1).split (· == '*')
  let lon_parts := (lon_str.dropRight 1).split (· == '*')
  (String.length lat_parts[0]! = 3 ∧ String.length lon_parts[0]! = 3) ∧
  let lat_min_sec := lat_parts[1]!.split (· == '\'')
  let lon_min_sec := lon_parts[1]!.split (· == '\'')
  (String.length lat_min_sec[0]! = 2 ∧ String.length lon_min_sec[0]! = 2) ∧
  (String.length lat_min_sec[1]! = 7 ∧ String.length lon_min_sec[1]! = 7) :=
sorry
-- </vc-theorems>