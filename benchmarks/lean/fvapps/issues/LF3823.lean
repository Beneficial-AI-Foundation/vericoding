-- <vc-preamble>
def radix_tree (words: List String) : NodeMap :=
  sorry

def reconstruct_word (t: NodeMap) : String :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_all_prefixes (t: NodeMap) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem radix_tree_empty_input :  
  ∀ (words: List String), 
  (∀ w ∈ words, w = "") → 
  radix_tree words = NodeMap.leaf :=
sorry

theorem radix_tree_deterministic :
  ∀ (words: List String),
  radix_tree words = radix_tree words :=
sorry 

theorem radix_tree_order_independent :
  ∀ (words₁ words₂: List String),
  words₁.length = words₂.length →
  (∀ w, w ∈ words₁ ↔ w ∈ words₂) →
  radix_tree words₁ = radix_tree words₂ :=
sorry

theorem radix_tree_single_word :
  ∀ (w: String),
  w ≠ "" →
  reconstruct_word (radix_tree [w]) = w :=
sorry

theorem radix_tree_prefixes_shared :
  ∀ (words: List String) (p: String),
  p ∈ get_all_prefixes (radix_tree words) →
  ∃ w₁ w₂, w₁ ∈ words ∧ w₂ ∈ words ∧ w₁ ≠ w₂ :=
sorry

/-
info: {}
-/
-- #guard_msgs in
-- #eval radix_tree ""

/-
info: {'ap': {'e': {}, 'ple': {}}}
-/
-- #guard_msgs in
-- #eval radix_tree "ape" "apple"

/-
info: {'rom': {'an': {'e': {}, 'us': {}}, 'ulus': {}}}
-/
-- #guard_msgs in
-- #eval radix_tree "romane" "romanus" "romulus"
-- </vc-theorems>