-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def identify_weapon (character : String) : String := sorry

theorem identify_weapon_valid_character (character : String) 
  (h : character = "Laval" ∨ 
       character = "Cragger" ∨ 
       character = "Lagravis" ∨
       character = "Crominus" ∨
       character = "Tormak" ∨ 
       character = "LiElla") :
  identify_weapon character = match character with
    | "Laval" => "Laval-Shado Valious"
    | "Cragger" => "Cragger-Vengdualize" 
    | "Lagravis" => "Lagravis-Blazeprowlor"
    | "Crominus" => "Crominus-Grandorius"
    | "Tormak" => "Tormak-Tygafyre"
    | "LiElla" => "LiElla-Roarburn"
    | _ => "Not a character" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem identify_weapon_invalid_character (character : String)
  (h : character ≠ "Laval" ∧
       character ≠ "Cragger" ∧
       character ≠ "Lagravis" ∧
       character ≠ "Crominus" ∧
       character ≠ "Tormak" ∧
       character ≠ "LiElla") :
  identify_weapon character = "Not a character" := sorry
-- </vc-theorems>