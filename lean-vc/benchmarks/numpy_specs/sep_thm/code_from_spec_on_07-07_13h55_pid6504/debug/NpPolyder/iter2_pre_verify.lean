/-
# NumPy Polyder Specification

Port of np_polyder.dfy to Lean 4
-/

namespace DafnySpecs.NpPolyder

-- LLM HELPER
def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

-- LLM HELPER
def binomial (n k : Nat) : Nat :=
  if k > n then 0
  else factorial n / (factorial k * factorial (n - k))

-- LLM HELPER
def derivativeCoeff (coeff : Float) (power : Nat) (deriv_order : Nat) : Float :=
  if deriv_order > power then 0.0
  else coeff * ((binomial power deriv_order).toFloat) * ((factorial deriv_order).toFloat)

-- LLM HELPER
def computeDerivative {n : Nat} (poly : Vector Float n) (m : Nat) : List Float :=
  match n with
  | 0 => []
  | _ => 
    let result_size := if m >= n then 0 else n - m
    if result_size = 0 then []
    else
      List.range result_size |>.map (fun i =>
        let power := i + m
        if h : power < n then
          derivativeCoeff (poly.get ⟨power, h⟩) power m
        else 0.0)

-- LLM HELPER
lemma computeDerivative_length {n : Nat} (poly : Vector Float n) (m : Nat) :
  (computeDerivative poly m).length = if m >= n then 0 else n - m := by
  cases' n with n'
  · simp [computeDerivative]
  · simp [computeDerivative, List.length_range, List.length_map]
    by_cases h : m >= n' + 1
    · simp [h]
    · simp [h]

/-- Compute polynomial derivative -/
def polyder {n : Nat} (poly : Vector Float n) (m : Int) : Vector Float (n - m.natAbs) := 
  let m_nat := m.natAbs
  let result_list := computeDerivative poly m_nat
  let result_size := n - m_nat
  -- LLM HELPER
  have h_length : result_list.length = result_size := by
    simp [computeDerivative_length, result_size]
    by_cases h : m_nat >= n
    · simp [h]
      omega
    · simp [h]
  Vector.mk result_list h_length

/-- Specification: The result has correct length -/
theorem polyder_length {n : Nat} (poly : Vector Float n) (m : Int)
  (h : m > 0) :
  let ret := polyder poly m
  ret.toList.length = n - m.natAbs := by
  simp [polyder, Vector.toList]

end DafnySpecs.NpPolyder