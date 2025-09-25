-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fly_by (lamps : String) (drone : String) : String := sorry

def countChar (s : String) (c : Char) : Nat :=
  s.data.filter (· = c) |>.length
-- </vc-definitions>

-- <vc-theorems>
theorem fly_by_length_preservation {lamps drone : String} 
  (h1 : lamps.all (· = 'x')) 
  (h2 : drone.all (fun c => c = '=' ∨ c = 'T')) :
  (fly_by lamps drone).length = lamps.length := sorry

theorem fly_by_valid_chars {lamps drone : String}
  (h1 : lamps.all (· = 'x'))
  (h2 : drone.all (fun c => c = '=' ∨ c = 'T')) :
  (fly_by lamps drone).all (fun c => c = 'o' ∨ c = 'x') := sorry

theorem fly_by_o_count {lamps drone : String}
  (h1 : lamps.all (· = 'x'))
  (h2 : drone.all (fun c => c = '=' ∨ c = 'T'))
  (h3 : drone.endsWith "T") :
  let result := fly_by lamps drone
  let num_os := countChar result 'o'
  num_os = min (countChar drone '=' + 1) lamps.length := sorry

theorem fly_by_unchanged_suffix {lamps drone : String}
  (h1 : lamps.all (· = 'x'))
  (h2 : drone.all (fun c => c = '=' ∨ c = 'T'))
  (h3 : drone.endsWith "T") :
  let result := fly_by lamps drone
  let num_os := countChar result 'o'
  result.drop num_os = String.mk (List.replicate (lamps.length - num_os) 'x') := sorry

theorem fly_by_minimal_drone {lamps : String}
  (h : lamps.all (· = 'x'))
  (h2 : lamps.length > 0) :
  let result := fly_by lamps "T"
  result.get! 0 = 'o' ∧ 
  result.drop 1 = lamps.drop 1 := sorry
-- </vc-theorems>