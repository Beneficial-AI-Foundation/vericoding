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
| x :: xs => x + sum_list xs

-- LLM HELPER
def prod_list : List Int → Int
| [] => 1
| x :: xs => x * prod_list xs

def implementation (numbers: List Int) : (Int × Int) := 
  (sum_list numbers, prod_list numbers)

-- LLM HELPER
lemma sum_list_cons (x : Int) (xs : List Int) : 
  sum_list (x :: xs) = x + sum_list xs := by
  rfl

-- LLM HELPER
lemma prod_list_cons (x : Int) (xs : List Int) : 
  prod_list (x :: xs) = x * prod_list xs := by
  rfl

-- LLM HELPER
lemma sum_list_nil : sum_list [] = 0 := by
  rfl

-- LLM HELPER
lemma prod_list_nil : prod_list [] = 1 := by
  rfl

-- LLM HELPER
lemma list_head_tail_eq (numbers : List Int) (h : numbers ≠ []) : 
  numbers[0]! = numbers.head (List.ne_nil_of_mem (List.mem_of_ne_nil h)) := by
  cases numbers with
  | nil => contradiction
  | cons x xs => simp [List.get!_cons_zero]

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers := by
  simp [problem_spec, implementation]
  use (sum_list numbers, prod_list numbers)
  simp
  constructor
  · intro h
    simp [h, sum_list_nil, prod_list_nil]
  · intro h
    simp [implementation]
    cases numbers with
    | nil => contradiction
    | cons x xs => 
      simp [sum_list_cons, prod_list_cons]
      constructor
      · ring
      · ring