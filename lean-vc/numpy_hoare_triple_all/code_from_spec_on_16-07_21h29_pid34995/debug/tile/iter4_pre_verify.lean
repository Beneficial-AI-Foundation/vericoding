import Std.Do.Triple
import Std.Tactic.Do

def tile {α : Type} {n : Nat} (A : Vector α n) (reps : Nat) : Id (Vector α (n * reps)) :=
  Id.pure ⟨(List.range reps |>.flatMap (fun _ => A.toList)), by
    rw [List.length_flatMap]
    simp [List.length_range, List.sum_replicate]
    rw [List.length_toList]
    ring⟩

-- LLM HELPER
structure HoareTriple (P : Prop) (M : Type) (Q : M → Prop) : Prop where
  triple : P → ∀ r : M, Q r

-- LLM HELPER
notation "⦃⌜" P "⌝⦄" M "⦃⇓result => ⌜" Q "⌝⦄" => HoareTriple P M (fun result => Q)

-- LLM HELPER
lemma List.length_flatMap_range_replicate {α : Type} (l : List α) (reps : Nat) :
  (List.range reps |>.flatMap (fun _ => l)).length = reps * l.length := by
  induction reps with
  | zero => simp [List.range, List.flatMap]
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp [List.flatMap_cons, List.length_append]
    ring

-- LLM HELPER
lemma List.get_flatMap_range_replicate {α : Type} (l : List α) (reps : Nat) (i : Fin (reps * l.length)) :
  (List.range reps |>.flatMap (fun _ => l)).get i = l.get ⟨i.val % l.length, by
    cases l.length with
    | zero => 
      simp at i
      exact absurd i.isLt (Nat.not_lt_zero _)
    | succ n => exact Nat.zero_lt_succ n⟩ := by
  cases reps with
  | zero => 
    simp at i
    exact absurd i.isLt (Nat.not_lt_zero _)
  | succ n =>
    induction n with
    | zero =>
      simp [List.range, List.flatMap]
      simp [List.range_succ, List.flatMap_cons, List.flatMap_nil]
      have : i.val < l.length := by
        simp at i
        exact i.isLt
      rw [List.get_append_left]
      · simp [Nat.mod_eq_of_lt this]
      · exact this
    | succ m ih =>
      simp [List.range_succ, List.flatMap_cons]
      by_cases h : i.val < l.length
      · rw [List.get_append_left _ h]
        simp [Nat.mod_eq_of_lt h]
      · rw [List.get_append_right]
        · have : i.val - l.length < (m + 1) * l.length := by
            have : i.val < (m + 2) * l.length := i.isLt
            simp at this
            omega
          rw [ih ⟨i.val - l.length, this⟩]
          congr 1
          rw [Nat.sub_mod]
          exact h
        · exact h

-- LLM HELPER
lemma Vector.get_mk {α : Type} {n : Nat} (l : List α) (h : l.length = n) (i : Fin n) :
  (Vector.mk l).get i = l.get ⟨i.val, by rw [← h]; exact i.isLt⟩ := by
  rfl

-- LLM HELPER
lemma List.get_toList {α : Type} {n : Nat} (v : Vector α n) (i : Fin n) :
  v.toList.get i = v.get i := by
  rfl

theorem tile_spec {α : Type} {n : Nat} (A : Vector α n) (reps : Nat) (h_reps : reps > 0) :
    HoareTriple (reps > 0) (Id (Vector α (n * reps))) (fun result => ∀ i : Fin (n * reps), result.get i = A.get ⟨i.val % n, by
      cases n with
      | zero =>
        simp at i
        exact absurd i.isLt (Nat.not_lt_zero _)
      | succ n' =>
        exact Nat.mod_lt i.val (Nat.zero_lt_succ n')
    ⟩) := by
  constructor
  intro h
  simp [tile, Id.pure]
  intro i
  have h_len : (List.range reps |>.flatMap (fun _ => A.toList)).length = n * reps := by
    rw [List.length_flatMap_range_replicate]
    simp [List.length_toList]
    ring
  have h_get : (List.range reps |>.flatMap (fun _ => A.toList)).get ⟨i.val, by rw [h_len]; exact i.isLt⟩ = 
               A.toList.get ⟨i.val % n, by
                 cases n with
                 | zero =>
                   simp at i
                   exact absurd i.isLt (Nat.not_lt_zero _)
                 | succ n' =>
                   rw [List.length_toList]
                   exact Nat.mod_lt i.val (Nat.zero_lt_succ n')
               ⟩ := by
    rw [List.get_flatMap_range_replicate]
    rw [List.length_toList]
  rw [Vector.get_mk, h_get, List.get_toList]