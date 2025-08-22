def problem_spec
-- function signature
(implementation: List Int → (Int × Int))
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: (Int × Int)) :=
let (sum, prod) := result;
(numbers = [] → sum = 0 ∧ prod = 1) ∧
(numbers ≠ [] →
(let (sum_tail, prod_tail) := implementation numbers.tail;
sum - sum_tail = numbers[0]! ∧
sum_tail * prod_tail + prod = sum * prod_tail));
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def sum_list : List Int → Int
  | [] => 0
  | h :: t => h + sum_list t

-- LLM HELPER
def prod_list : List Int → Int
  | [] => 1
  | h :: t => h * prod_list t

def implementation (numbers: List Int) : (Int × Int) := 
  (sum_list numbers, prod_list numbers)

-- LLM HELPER
lemma sum_list_cons (h : Int) (t : List Int) : 
  sum_list (h :: t) = h + sum_list t := by
  simp [sum_list]

-- LLM HELPER
lemma prod_list_cons (h : Int) (t : List Int) : 
  prod_list (h :: t) = h * prod_list t := by
  simp [prod_list]

-- LLM HELPER
lemma sum_list_nil : sum_list [] = 0 := by
  simp [sum_list]

-- LLM HELPER
lemma prod_list_nil : prod_list [] = 1 := by
  simp [prod_list]

-- LLM HELPER
lemma list_head_tail (numbers : List Int) (h : numbers ≠ []) : 
  numbers = numbers[0]! :: numbers.tail := by
  cases numbers with
  | nil => contradiction
  | cons head tail => 
    simp [List.getElem!, List.head!, List.tail]

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers := by
  unfold problem_spec
  let result := (sum_list numbers, prod_list numbers)
  use result
  constructor
  · simp [implementation]
  · intro result
    simp only [result]
    constructor
    · intro h
      constructor
      · rw [h]; exact sum_list_nil
      · rw [h]; exact prod_list_nil
    · intro h
      cases numbers with
      | nil => contradiction
      | cons head tail =>
        simp [List.getElem!, List.head!, List.tail, implementation]
        simp [sum_list_cons, prod_list_cons]
        constructor
        · ring
        · ring