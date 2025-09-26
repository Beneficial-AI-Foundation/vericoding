import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- no additional helpers required
-- </vc-helpers>

-- <vc-definitions>
def RotateRight (l : Array Int) (n : Int) : Array Int :=
if h : l.size = 0 then
  l
else
  let sz := l.size
  let szI := (Int.ofNat sz)
  Array.ofFn (fun i : Fin sz =>
    let srcI := ((Int.ofNat (i : Nat)) - n + szI) % szI
    l[srcI.toNat]!)
-- </vc-definitions>

-- <vc-theorems>
theorem RotateRight_spec (l : Array Int) (n : Int) :
n ≥ 0 →
let r := RotateRight l n
(r.size = l.size) ∧
(∀ i, 0 ≤ i ∧ i < l.size →
r[i]! = l[((i - n + l.size) % l.size).toNat]!) :=
by
  intro hn
  classical
  change
    (RotateRight l n).size = l.size ∧
      (∀ i, 0 ≤ i ∧ i < l.size →
        (RotateRight l n)[i]! =
          l[((i - n + l.size) % l.size).toNat]!)
  by_cases hsz : l.size = 0
  · constructor
    · simp [RotateRight, hsz]
    · intro i hi
      have hnot : ¬ i < l.size := by
        simpa [hsz] using (Nat.not_lt.mpr (Nat.zero_le i))
      exact (hnot hi.2).elim
  · constructor
    · simp [RotateRight, hsz]
    · intro i hi
      have hi' : i < l.size := hi.2
      simpa [RotateRight, hsz, hi']
-- </vc-theorems>
