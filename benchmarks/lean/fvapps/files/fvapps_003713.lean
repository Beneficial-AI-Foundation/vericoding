-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def howmuch (m n : Int) : List (List String) := sorry

theorem howmuch_result_format {m n : Int} (h : -1000 ≤ m ∧ m ≤ 1000) (h' : -1000 ≤ n ∧ n ≤ 1000) :
  let result := howmuch m n
  ∀ item ∈ result,
    item.length = 3 ∧
    (∃ m_val b_val c_val : Int,
      item.get! 0 = s!"M: {m_val}" ∧
      item.get! 1 = s!"B: {b_val}" ∧
      item.get! 2 = s!"C: {c_val}") := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem howmuch_values_satisfy_conditions {m n : Int} (h : -1000 ≤ m ∧ m ≤ 1000) (h' : -1000 ≤ n ∧ n ≤ 1000) :
  let result := howmuch m n
  ∀ item ∈ result,
    let m_val := (item.get! 0).drop 3 |>.toInt!
    let b_val := (item.get! 1).drop 3 |>.toInt!
    let c_val := (item.get! 2).drop 3 |>.toInt!
    m_val % 7 = 2 ∧
    m_val % 9 = 1 ∧
    m_val / 7 = b_val ∧  
    m_val / 9 = c_val ∧
    min m n ≤ m_val ∧ m_val ≤ max m n := sorry

theorem howmuch_identical_inputs {x : Int} (h : -1000 ≤ x ∧ x ≤ 1000) :
  let result := howmuch x x
  ∀ item ∈ result,
    ((item.get! 0).drop 3 |>.toInt!) = x := sorry
-- </vc-theorems>