-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def interpreter (s : String) : String := sorry

theorem interpreter_output_is_string
  (commands : String)
  (h : ∀ c ∈ commands.toList, c ∈ ['>','<','!','*','+','-','/']) :
  ∃ s : String, interpreter commands = s := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem interpreter_chr_range
  (commands : String)
  (h : ∀ c ∈ commands.toList, c ∈ ['>','<','!','*','+','-','/']) :
  ∀ c ∈ (interpreter commands).toList, 
    0 ≤ c.toNat ∧ c.toNat < 256 := sorry

theorem increment_decrement_cancellation
  (commands : String)
  (h₁ : ∀ c ∈ commands.toList, c ∈ ['+','-'])
  (h₂ : commands.toList.length > 0)
  (h₃ : (commands.toList.filter (fun x => x = '+')).length = 
        (commands.toList.filter (fun x => x = '-')).length) :
  interpreter commands = "" ∨ 
  ∀ c ∈ (interpreter commands).toList, c.toNat = 0 := sorry

theorem memory_pointer_bounds
  (commands : String)
  (h : ∀ c ∈ commands.toList, c ∈ ['>','<','!','*','+','-','/']) :
  ∃ s : String, interpreter commands = s := sorry

theorem clear_cell
  (commands : String)
  (h₁ : ∀ c ∈ commands.toList, c = '/')
  (h₂ : commands.toList.length > 0) :
  interpreter (commands ++ "*") = "\u0000" := sorry

theorem new_cells_initialized_zero
  (commands : String)
  (h : ∀ c ∈ commands.toList, c ∈ ['>','!']) :
  interpreter (commands ++ "*") = "\u0000" := sorry
-- </vc-theorems>