-- <vc-helpers>
-- </vc-helpers>

def capitalize (s : String) : List String := sorry

theorem capitalize_returns_two_strings (s : String) :
  let result := capitalize s
  List.length result = 2 := by sorry

theorem capitalize_elements_are_strings (s : String) :
  let result := capitalize s
  result.all (fun x => true) := by sorry

theorem capitalize_second_equals_first (s : String) :
  let result := capitalize s
  result.get! 1 = result.get! 0 := by sorry

theorem capitalize_empty_string :
  capitalize "" = ["", ""] := by sorry

-- Apps difficulty: introductory
-- Assurance level: guarded