namespace NpCumSum

def cumSum {n : Nat} (a : Vector Int n) : Vector Int n := 
  match n with
  | 0 => Vector.nil
  | n + 1 => 
    let rec helper (i : Nat) (acc : Int) : List Int :=
      if h : i < n + 1 then
        let curr := acc + a[i]'h
        curr :: helper (i + 1) curr
      else
        []
    Vector.ofFn (fun i => 
      let rec cumAtIndex (j : Nat) (sum : Int) : Int :=
        if h : j <= i.val then
          if j = i.val then
            sum + a[j]'(by omega)
          else
            cumAtIndex (j + 1) (sum + a[j]'(by omega))
        else
          sum
      cumAtIndex 0 0)

theorem cumSum_spec {n : Nat} (a : Vector Int n) :
  (cumSum a)[0]'(by omega) = a[0]'(by omega) ∧
  ∀ i : Fin n, i.val > 0 → (cumSum a)[i] = (cumSum a)[i.val - 1]'(by omega) + a[i] := by
  constructor
  · -- First part: (cumSum a)[0] = a[0]
    simp [cumSum]
    sorry
  · -- Second part: for i > 0, (cumSum a)[i] = (cumSum a)[i-1] + a[i]
    intro i hi
    simp [cumSum]
    sorry

end NpCumSum