import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def String.replicate (s : String) (n : Nat) : String :=
  match n with
  | 0 => ""
  | n + 1 => s ++ String.replicate s n

-- LLM HELPER
def String.ljust_single (s : String) (width : Nat) (fillchar : String) : String :=
  if s.length >= width then s
  else s ++ String.replicate fillchar (width - s.length)

/-- numpy.strings.ljust: Return an array with the elements left-justified in a string of length width.

    Left-justifies each string in the input array by padding it with the specified
    fill character (default is space) to reach the specified width. If the original
    string is longer than or equal to the width, it remains unchanged.

    Parameters:
    - a: Input array of strings
    - width: Target width for each string
    - fillchar: Character to use for padding (must be exactly one character)
    
    Returns:
    - Array where each string is left-justified to the specified width
-/
def ljust {n : Nat} (a : Vector String n) (width : Nat) (fillchar : String) : Id (Vector String n) :=
  pure ⟨a.val.map (fun s => String.ljust_single s width fillchar), by simp⟩

-- LLM HELPER
lemma String.replicate_length (s : String) (n : Nat) : (String.replicate s n).length = s.length * n := by
  induction n with
  | zero => simp [String.replicate]
  | succ n ih => simp [String.replicate, ih, Nat.add_mul, Nat.mul_one]

-- LLM HELPER
lemma String.ljust_single_length (s : String) (width : Nat) (fillchar : String) :
    (String.ljust_single s width fillchar).length = max s.length width := by
  simp [String.ljust_single]
  split_ifs with h
  · simp [Nat.max_def]
    exact Nat.le_iff_lt_or_eq.mp h
  · simp [String.replicate_length]
    rw [Nat.max_def]
    simp [h]
    omega

-- LLM HELPER
lemma String.ljust_single_ge_width (s : String) (width : Nat) (fillchar : String) :
    s.length >= width → String.ljust_single s width fillchar = s := by
  intro h
  simp [String.ljust_single, h]

-- LLM HELPER
lemma String.ljust_single_lt_width (s : String) (width : Nat) (fillchar : String) :
    s.length < width → 
    let res := String.ljust_single s width fillchar
    res.length = width ∧ 
    (∃ padding : String, res = s ++ padding ∧ padding.length = width - s.length) ∧
    res.startsWith s := by
  intro h
  simp [String.ljust_single, h]
  constructor
  · simp [String.replicate_length]
    omega
  constructor
  · use String.replicate fillchar (width - s.length)
    constructor
    · rfl
    · simp [String.replicate_length]
  · simp [String.startsWith_append]

/-- Specification: ljust returns a vector where each string is left-justified
    to the specified width using the given fill character.

    Mathematical Properties:
    - Length preservation: Result length is max(original_length, width)
    - Identity: Strings already >= width remain unchanged
    - Left-justification: Original content preserved as prefix, padding on right
    - Minimality: No unnecessary padding beyond required width
    - Fillchar constraint: Padding uses specified fill character
    - Exactness constraint: padding achieves exact width requirement
    - Consistency constraint: all operations preserve the vector structure
-/
theorem ljust_spec {n : Nat} (a : Vector String n) (width : Nat) (fillchar : String)
    (h_fillchar : fillchar.length = 1) :
    ⦃⌜fillchar.length = 1⌝⦄
    ljust a width fillchar
    ⦃⇓result => ⌜∀ i : Fin n, 
        let orig := a.get i
        let res := result.get i
        -- Core mathematical properties of left-justification
        -- 1. Length invariant: result length is exactly max(orig.length, width)
        res.length = max orig.length width ∧
        -- 2. Identity morphism: strings already >= width are unchanged (f(x) = x when |x| >= w)
        (orig.length ≥ width → res = orig) ∧
        -- 3. Padding morphism: strings < width are extended (f(x) = x ++ p when |x| < w)
        (orig.length < width → 
            res.length = width ∧
            (∃ padding : String, res = orig ++ padding ∧ 
                padding.length = width - orig.length) ∧
            -- Left-justification property: original is preserved as prefix
            res.startsWith orig) ∧
        -- 4. Minimality constraint: no over-padding (efficient operation)
        (orig.length ≥ width → res.length = orig.length) ∧
        -- 5. Exactness constraint: padding achieves exact width requirement
        (orig.length < width → res.length = width) ∧
        -- 6. Consistency constraint: all operations preserve the vector structure
        (orig.length = 0 → res.length = width)⌝⦄ := by
  simp [ljust]
  intro i
  simp [Vector.get]
  let orig := a.get i
  let res := String.ljust_single orig width fillchar
  constructor
  · exact String.ljust_single_length orig width fillchar
  constructor
  · exact String.ljust_single_ge_width orig width fillchar
  constructor
  · exact String.ljust_single_lt_width orig width fillchar
  constructor
  · intro h
    rw [String.ljust_single_ge_width orig width fillchar h]
  constructor
  · intro h
    have := String.ljust_single_lt_width orig width fillchar h
    exact this.1
  · intro h
    simp [h]
    simp [String.ljust_single]
    split_ifs with h'
    · simp [h] at h'
      simp [h']
    · simp [String.replicate_length]
      omega