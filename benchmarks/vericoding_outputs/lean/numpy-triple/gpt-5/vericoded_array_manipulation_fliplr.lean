import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/-- Reverse an index in `Fin n` by mirroring around the right end. For length `n+1`,
this sends `j` to `n - j` so that `j + (rev j) = n`. -/
def finRev (n : Nat) : Fin n → Fin n :=
  match n with
  | 0 => fun j => nomatch j
  | Nat.succ n => fun j => ⟨n - j.val, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩

@[simp] theorem finRev_succ_val {n : Nat} (j : Fin (n+1)) :
  (finRev (n+1) j).val = n - j.val := rfl

/-- For length `n+1`, the sum of an index and its reversed index equals `n`. -/
 theorem finRev_sum {n : Nat} (j : Fin (n+1)) :
  j.val + (finRev (n+1) j).val = n := by
  have hjle : j.val ≤ n := Nat.le_of_lt_succ j.isLt
  simp [finRev_succ_val, Nat.add_sub_of_le hjle]

/-- Reversing twice is the identity for length `n+1`. -/
 theorem finRev_involutive {n : Nat} (j : Fin (n+1)) :
  finRev (n+1) (finRev (n+1) j) = j := by
  apply Fin.ext
  have hjle : j.val ≤ n := Nat.le_of_lt_succ j.isLt
  simp [finRev_succ_val, Nat.sub_sub_self hjle]

/-- If `2 * j = n`, then `j` is a fixed point of `finRev (n+1)`. -/
 theorem finRev_fixed_of_two_mul_eq {n : Nat} {j : Fin (n+1)} (h : 2 * j.val = n) :
  finRev (n+1) j = j := by
  apply Fin.ext
  have hn : n = j.val + j.val := by
    simpa [two_mul] using h.symm
  have : n - j.val = j.val := by
    simpa [hn] using (Nat.add_sub_cancel j.val j.val)
  simpa [finRev_succ_val, this]

@[simp] theorem Vector.get_ofFn' {α} {n : Nat} (f : Fin n → α) (i : Fin n) :
  (Vector.ofFn f).get i = f i := by
  simpa using Vector.get_ofFn f i

@[simp] theorem Vector.get_ofFn2 {α} {m n : Nat} (f : Fin m → Fin n → α)
    (i : Fin m) (j : Fin n) :
  ((Vector.ofFn (fun i => Vector.ofFn (f i))).get i).get j = f i j := by
  simp
-- </vc-helpers>

-- <vc-definitions>
def fliplr {rows cols : Nat} (m : Vector (Vector Float cols) rows) : Id (Vector (Vector Float cols) rows) :=
  pure <|
  Vector.ofFn (fun i : Fin rows =>
    Vector.ofFn (fun j : Fin cols =>
      (m.get i).get (finRev cols j)))
-- </vc-definitions>

-- <vc-theorems>
theorem fliplr_spec {rows : Nat} {cols : Nat} (m : Vector (Vector Float (cols + 1)) rows) :
    ⦃⌜True⌝⦄
    fliplr m
    ⦃⇓result => ⌜(∀ i : Fin rows, ∀ j : Fin (cols + 1), 
                   ∃ k : Fin (cols + 1), 
                   (result.get i).get j = (m.get i).get k ∧ 
                   j.val + k.val = cols) ∧
                 (∀ i : Fin rows, 
                   (∀ x : Float, (∃ j : Fin (cols + 1), (m.get i).get j = x) ↔ 
                                 (∃ j : Fin (cols + 1), (result.get i).get j = x))) ∧
                 (cols % 2 = 0 → 
                   ∀ i : Fin rows, 
                   ∃ mid : Fin (cols + 1),
                   2 * mid.val = cols ∧
                   (result.get i).get mid = (m.get i).get mid)⌝⦄ := by
  simpa [fliplr] using
    (fun (_h : True) => by
      constructor
      · intro i j
        refine ⟨finRev (cols + 1) j, ?_⟩
        constructor
        · simp [Vector.get_ofFn2]
        · simpa using (finRev_sum (n := cols) j)
      · constructor
        · intro i x
          constructor
          · intro hx
            rcases hx with ⟨j, hj⟩
            refine ⟨finRev (cols + 1) j, ?_⟩
            simpa [Vector.get_ofFn2, finRev_involutive] using hj
          · intro hx
            rcases hx with ⟨j, hj⟩
            refine ⟨finRev (cols + 1) j, ?_⟩
            simpa [Vector.get_ofFn2] using hj
        · intro hEven i
          have hdiv : 2 ∣ cols := Nat.dvd_of_mod_eq_zero hEven
          rcases hdiv with ⟨t, ht⟩
          have hle : t ≤ cols := by
            have : t ≤ t + t := Nat.le_add_left _ _
            simpa [two_mul, ht] using this
          let mid : Fin (cols + 1) := ⟨t, Nat.lt_succ_of_le hle⟩
          refine ⟨mid, ?_, ?_⟩
          · simpa [two_mul, mid] using ht.symm
          ·
            have h2 : 2 * mid.val = cols := by simpa [two_mul, mid] using ht.symm
            have hf : finRev (cols + 1) mid = mid :=
              finRev_fixed_of_two_mul_eq (n := cols) (j := mid) h2
            simp [Vector.get_ofFn2, hf])
-- </vc-theorems>
