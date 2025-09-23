-- <vc-preamble>
def Set (α : Type) := α → Prop

def find_seventh_sons_of_seventh_sons (json : String) : Set String :=
  sorry

def fromJson? (s : String) : Option Person :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def collectNames (p : Person) : Set String :=
  sorry

/- Theorems about find_seventh_sons_of_seventh_sons -/
-- </vc-definitions>

-- <vc-theorems>
theorem empty_tree (p : Person) (h : match p with | Person.mk _ _ children => children = []) :
  find_seventh_sons_of_seventh_sons (toString p) = λ _ => False :=
sorry

theorem result_is_subset (json : String) (tree : Person) (h : fromJson? json = some tree) :
  let result := find_seventh_sons_of_seventh_sons json
  let names := collectNames tree
  ∀ x, result x → names x :=
sorry

theorem leaf_nodes (name : String) (p : Person) 
  (h₁ : match p with | Person.mk n _ _ => n = name)
  (h₂ : match p with | Person.mk _ g _ => g = "male") 
  (h₃ : match p with | Person.mk _ _ c => c = []) :
  find_seventh_sons_of_seventh_sons (toString p) = λ _ => False :=
sorry

theorem seventh_son_pattern (root father seventhSon seventhGrandson : Person)
  (h₁ : match father with | Person.mk _ g _ => g = "male")
  (h₂ : match father with | Person.mk _ _ c => List.length c = 7) 
  (h₃ : ∃ children, match father with | Person.mk _ _ c => c = children ∧ children.get? 6 = some seventhSon)
  (h₄ : match seventhSon with | Person.mk _ g _ => g = "male")
  (h₅ : match seventhSon with | Person.mk _ _ c => List.length c = 7)
  (h₆ : ∃ children, match seventhSon with | Person.mk _ _ c => c = children ∧ children.get? 6 = some seventhGrandson)
  (h₇ : match seventhGrandson with | Person.mk n _ _ => n = "grandson7") :
  (find_seventh_sons_of_seventh_sons (toString root)) "grandson7" :=
sorry

/-
info: set()
-/
-- #guard_msgs in
-- #eval find_seventh_sons_of_seventh_sons "\n    {\n        "name": "John",\n        "gender": "male",\n        "children": [\n            {"name": "Bob", "gender": "male", "children": []},\n            {"name": "Amy", "gender": "female", "children": []}\n        ]\n    }\n    "

/-
info: {'Target'}
-/
-- #guard_msgs in
-- #eval find_seventh_sons_of_seventh_sons "\n    {\n        "name": "Root",\n        "gender": "male",\n        "children": [\n            {\n                "name": "Dad",\n                "gender": "male",\n                "children": [\n                    {"name": "Son1", "gender": "male", "children": []},\n                    {"name": "Son2", "gender": "male", "children": []},\n                    {"name": "Son3", "gender": "male", "children": []},\n                    {"name": "Son4", "gender": "male", "children": []},\n                    {"name": "Son5", "gender": "male", "children": []},\n                    {"name": "Son6", "gender": "male", "children": []},\n                    {\n                        "name": "Son7",\n                        "gender": "male",\n                        "children": [\n                            {"name": "GSon1", "gender": "male", "children": []},\n                            {"name": "GSon2", "gender": "male", "children": []},\n                            {"name": "GSon3", "gender": "male", "children": []},\n                            {"name": "GSon4", "gender": "male", "children": []},\n                            {"name": "GSon5", "gender": "male", "children": []},\n                            {"name": "GSon6", "gender": "male", "children": []},\n                            {"name": "Target", "gender": "male", "children": []}\n                        ]\n                    }\n                ]\n            }\n        ]\n    }\n    "
-- </vc-theorems>