-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def interpreter (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_valid_chars {tape : String} 
  (h : String.contains tape '&') :
  ∀ c, c ∈ (interpreter tape).data → 0 ≤ Char.toNat c ∧ Char.toNat c < 256 :=
sorry

theorem arithmetic_wrapping (n : Nat) :
  let tape := String.mk ((List.replicate n '+') ++ 
               (List.replicate n '-') ++ ['*', '&'])
  interpreter tape = "\u0000" :=
sorry
-- </vc-theorems>