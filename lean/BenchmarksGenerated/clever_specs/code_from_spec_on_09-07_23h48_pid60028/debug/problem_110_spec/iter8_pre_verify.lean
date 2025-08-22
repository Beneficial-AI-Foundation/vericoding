def problem_spec
(implementation: List Int → List Int → String)
(lst1: List Int)
(lst2: List Int) :=
let spec (result : String) :=
  lst1 ≠ [] → lst2 ≠ [] →
  let bool_result := ∃ exchange: List (Nat × Nat),
    let lst1_idxs := exchange.map (fun (a, b) => a)
    let lst2_idxs := exchange.map (fun (a, b) => b)
    lst1_idxs.all (fun i => i < lst1.length) ∧
    lst2_idxs.all (fun i => i < lst2.length) ∧
    lst1_idxs.Nodup ∧
    lst2_idxs.Nodup ∧
    ∀ i, i < lst1.length →
      (i ∉ lst1_idxs → Even (lst1[i]!)) ∧
      (i ∈ lst1_idxs →
        let i_idx := (lst1_idxs.idxOf i)
        Even (lst2[lst2_idxs[i_idx]!]!))
  (bool_result → result = "YES") ∧
  (¬bool_result → result = "NO") ∧
  (result ≠ "YES" ∧ result ≠ "NO" → False)
∃ result,
  implementation lst1 lst2 = result ∧
  spec result

-- LLM HELPER
def Even (n : Int) : Prop := ∃ k, n = 2 * k

-- LLM HELPER
def canSolve (lst1: List Int) (lst2: List Int) : Bool :=
  if lst1.isEmpty || lst2.isEmpty then true
  else
    let oddIndices1 := (List.range lst1.length).filter (fun i => ¬(lst1[i]!.natAbs % 2 = 0))
    let evenIndices2 := (List.range lst2.length).filter (fun i => (lst2[i]!.natAbs % 2 = 0))
    oddIndices1.length ≤ evenIndices2.length

def implementation (lst1: List Int) (lst2: List Int) : String := 
  if canSolve lst1 lst2 then "YES" else "NO"

-- LLM HELPER
lemma even_iff_natAbs_even (n : Int) : Even n ↔ Even n.natAbs := by
  constructor
  · intro h
    cases h with
    | intro k hk => 
      simp [Even, Int.natAbs]
      cases' n with n n
      · simp at hk
        use k.natAbs
        rw [hk]
        simp
      · simp at hk
        rw [hk]
        use k.natAbs
        simp
  · intro h
    cases h with
    | intro k hk =>
      simp [Even]
      cases' n with n n
      · simp [Int.natAbs] at hk
        use k
        simp [hk]
      · simp [Int.natAbs] at hk
        use -(k : Int)
        simp [hk]

-- LLM HELPER
lemma even_iff_mod_two (n : Int) : Even n ↔ n.natAbs % 2 = 0 := by
  rw [even_iff_natAbs_even]
  rw [Nat.even_iff_two_dvd]
  rw [Nat.dvd_iff_mod_eq_zero]

-- LLM HELPER
lemma empty_case (lst1 lst2 : List Int) (h1 : lst1 = [] ∨ lst2 = []) :
  ∃ exchange: List (Nat × Nat),
    let lst1_idxs := exchange.map (fun (a, b) => a)
    let lst2_idxs := exchange.map (fun (a, b) => b)
    lst1_idxs.all (fun i => i < lst1.length) ∧
    lst2_idxs.all (fun i => i < lst2.length) ∧
    lst1_idxs.Nodup ∧
    lst2_idxs.Nodup ∧
    ∀ i, i < lst1.length →
      (i ∉ lst1_idxs → Even (lst1[i]!)) ∧
      (i ∈ lst1_idxs →
        let i_idx := (lst1_idxs.idxOf i)
        Even (lst2[lst2_idxs[i_idx]!]!)) := by
  use []
  simp [List.all_nil, List.nodup_nil]
  intro i hi
  cases h1 with
  | inl h => simp [h] at hi
  | inr h => 
    constructor
    · intro _
      rw [even_iff_mod_two]
      simp
    · intro hcontra
      simp at hcontra

theorem correctness
(lst1: List Int)
(lst2: List Int)
: problem_spec implementation lst1 lst2 := by
  use implementation lst1 lst2
  constructor
  · rfl
  · intro h1 h2
    simp [implementation]
    by_cases h : canSolve lst1 lst2
    · simp [h]
      constructor
      · intro _
        rfl
      · constructor
        · intro hcontra
          simp at hcontra
        · intro hcontra
          cases hcontra with
          | inl hyes => simp at hyes
          | inr hno => simp at hno
    · simp [h]
      constructor
      · intro hcontra
        simp at hcontra
      · constructor
        · intro _
          simp [canSolve] at h
          simp [h1, h2] at h
          by_contra hex
          cases hex with
          | intro exchange hx =>
            simp [canSolve] at h
            simp [h1, h2] at h
            exact h rfl
        · intro hcontra
          cases hcontra with
          | inl hyes => simp at hyes
          | inr hno => simp at hno