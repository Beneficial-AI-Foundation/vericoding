import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
(∀ i: Int, i ∈ result → numbers.count i = 1) ∧
(∀ i: Int, i ∈ numbers → numbers.count i = 1 → i ∈ result) ∧
(∀ i j : Nat, i < result.length → j < result.length → i < j →
∃ ip jp : Nat, ip < jp ∧ result[i]! = numbers[ip]! ∧ result[j]! = numbers[jp]!)
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def filter_unique (numbers: List Int) : List Int :=
  numbers.filter (fun x => numbers.count x = 1)

def implementation (numbers: List Int) : List Int := filter_unique numbers

-- LLM HELPER
lemma mem_filter_unique_iff (numbers: List Int) (x: Int) : 
  x ∈ filter_unique numbers ↔ x ∈ numbers ∧ numbers.count x = 1 := by
  simp [filter_unique, List.mem_filter]

-- LLM HELPER
lemma filter_preserves_order (l: List Int) (p: Int → Bool) (i j: Nat) 
  (hi : i < (l.filter p).length) (hj : j < (l.filter p).length) (hij : i < j) :
  ∃ ip jp : Nat, ip < jp ∧ ip < l.length ∧ jp < l.length ∧ 
  (l.filter p)[i]'hi = l[ip]'(by omega) ∧ (l.filter p)[j]'hj = l[jp]'(by omega) := by
  have h1 : (l.filter p)[i]'hi ∈ l := List.mem_of_mem_filter (List.get_mem (l.filter p) i)
  have h2 : (l.filter p)[j]'hj ∈ l := List.mem_of_mem_filter (List.get_mem (l.filter p) j)
  let ip := l.indexOf (l.filter p)[i]'hi
  let jp := l.indexOf (l.filter p)[j]'hj
  have hip : ip < l.length := List.indexOf_lt_length.mpr h1
  have hjp : jp < l.length := List.indexOf_lt_length.mpr h2
  have h_ip_eq : l[ip]'hip = (l.filter p)[i]'hi := (List.getElem_indexOf h1).symm
  have h_jp_eq : l[jp]'hjp = (l.filter p)[j]'hj := (List.getElem_indexOf h2).symm
  have sublist : (l.filter p).Sublist l := List.filter_sublist p l
  have ip_lt_jp : ip < jp := List.Sublist.indexOf_lt_indexOf sublist (List.get_mem (l.filter p) i) (List.get_mem (l.filter p) j) hij
  use ip, jp
  exact ⟨ip_lt_jp, hip, hjp, h_ip_eq.symm, h_jp_eq.symm⟩

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  simp [problem_spec, implementation]
  use filter_unique numbers
  constructor
  · rfl
  · constructor
    · intro i hi
      rw [mem_filter_unique_iff] at hi
      exact hi.2
    · constructor
      · intro i hi hcount
        rw [mem_filter_unique_iff]
        exact ⟨hi, hcount⟩
      · intro i j hi hj hij
        simp [filter_unique]
        let filtered := numbers.filter (fun x => numbers.count x = 1)
        
        obtain ⟨ip, jp, hip_lt_jp, hip_bound, hjp_bound, h_eq_i, h_eq_j⟩ := 
          filter_preserves_order numbers (fun x => numbers.count x = 1) i j hi hj hij
        
        use ip, jp
        constructor
        · exact hip_lt_jp
        · constructor
          · rw [List.getElem!_pos numbers ip hip_bound]
            rw [h_eq_i]
            rw [List.getElem!_pos filtered i hi]
          · rw [List.getElem!_pos numbers jp hjp_bound]
            rw [h_eq_j]
            rw [List.getElem!_pos filtered j hj]