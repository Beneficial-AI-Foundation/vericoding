-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Value := String ⊕ Int

def unusual_sort (arr : List Value) : List Value :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem unusual_sort_preserves_length (arr : List Value) :
  (unusual_sort arr).length = arr.length :=
  sorry

theorem unusual_sort_preserves_elements (arr : List Value) :
  ∃ perm : List.Perm (unusual_sort arr) arr,
    ∀ x, x ∈ unusual_sort arr ↔ x ∈ arr :=
  sorry
-- </vc-theorems>