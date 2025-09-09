/-
Convert DD (decimal degrees) position to DMS (degrees, minutes, seconds).

##### Inputs:
`dd_lat` and `dd_lon` 2 strings representing the latitude and the longitude in degree -i.e. 2 floats included in [-90, 90] and [-180, 180]. Note that latitude 0 is north, longitude 0 is east.

##### Outputs:
A tuple of DMS latitudes formated as follows:
`DDD*mm'ss.sss"C`

With:
- `DDD`: degrees
- `mm`: minutes
- `ss.sss`: seconds rounded to 3 decimals
- `C`: first letter uppercase of the cardinal direction

##### ressources
about WGS 84 on [Wikipedia](https://en.wikipedia.org/wiki/World_Geodetic_System#WGS84)
-/

-- <vc-helpers>
-- </vc-helpers>

def convert_to_dms (lat: String) (lon: String) : String × String :=
  sorry

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

/-
info: ('035*01\'58.781"N', '033*14\'01.519"E')
-/
-- #guard_msgs in
-- #eval convert_to_dms "35.03299485527936" "33.233755230903625"

/-
info: ('037*06\'41.096"S', '012*17\'03.541"W')
-/
-- #guard_msgs in
-- #eval convert_to_dms "-37.111415669561595" "-12.284317023586482"

/-
info: ('019*36\'53.975"N', '155*28\'55.841"W')
-/
-- #guard_msgs in
-- #eval convert_to_dms "19.61499312350978" "-155.48217818140984"

-- Apps difficulty: introductory
-- Assurance level: unguarded