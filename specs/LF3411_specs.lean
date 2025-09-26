-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def say_hello (names: List String) (city state: String) : String := sorry 

def String.substringExists (s1 s2: String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem say_hello_contains_all_names (names: List String) (city state: String)
  (h1: names ≠ [])
  (h2: ∀ n ∈ names, n ≠ "") 
  (h3: city ≠ "")
  (h4: state ≠ "") :
  ∀ n ∈ names, String.substringExists (say_hello names city state) n := 
  sorry

theorem say_hello_contains_location (names: List String) (city state: String)  
  (h1: names ≠ [])
  (h2: ∀ n ∈ names, n ≠ "") 
  (h3: city ≠ "")
  (h4: state ≠ "") :
  String.substringExists (say_hello names city state) city ∧ 
  String.substringExists (say_hello names city state) state :=
  sorry

theorem say_hello_structure (names: List String) (city state: String)
  (h1: names ≠ [])
  (h2: ∀ n ∈ names, n ≠ "") 
  (h3: city ≠ "")
  (h4: state ≠ "") :
  let result := say_hello names city state
  (result.startsWith "Hello, " ∧ 
   String.substringExists result "! Welcome to " ∧
   result.endsWith (", " ++ state ++ "!")) :=
  sorry
-- </vc-theorems>