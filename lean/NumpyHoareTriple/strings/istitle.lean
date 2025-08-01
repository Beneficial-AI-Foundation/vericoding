import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.strings.istitle",
  "category": "String information",
  "description": "Returns true for each element if the element is a titlecased string and there is at least one character, false otherwise",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.istitle.html",
  "doc": "Returns true for each element if the element is a titlecased string and there is at least one character, false otherwise.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n\nReturns\n-------\nout : ndarray\n    Output array of bools",
  "code": "def istitle(a):\n    \"\"\"\n    Returns true for each element if the element is a titlecased\n    string and there is at least one character, false otherwise.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    Returns\n    -------\n    out : ndarray\n        Output array of bools\n\n    See Also\n    --------\n    str.istitle\n\n    Examples\n    --------\n    >>> np.strings.istitle(\"Numpy Is Great\")\n    array(True)\n\n    >>> np.strings.istitle(\"Numpy is great\")\n    array(False)\n\n    \"\"\"\n    a = np.asanyarray(a)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    return _istitle_ufunc(a)"
}
-/

open Std.Do

/-- Helper function to check if a string is titlecased according to Python's str.istitle() logic -/
def isTitlecased (s : String) : Bool :=
  if s.isEmpty then false
  else
    let chars := s.toList
    let hasCasedChar := chars.any (fun c => c.isUpper || c.isLower)
    if ¬hasCasedChar then false
    else
      -- Check title case: first cased char after non-cased char must be uppercase,
      -- subsequent cased chars must be lowercase until next non-cased char
      let rec checkTitleCase (cs : List Char) (expectUpper : Bool) : Bool :=
        match cs with
        | [] => true
        | c :: rest =>
          if c.isUpper then
            if expectUpper then checkTitleCase rest false
            else false
          else if c.isLower then
            if expectUpper then false
            else checkTitleCase rest false
          else
            -- Non-cased character, next cased char should be uppercase
            checkTitleCase rest true
      checkTitleCase chars true

/-- numpy.strings.istitle: Returns true for each element if the element is a titlecased string and there is at least one character, false otherwise.

    A string is considered titlecased if:
    1. It contains at least one character
    2. Each word starts with an uppercase letter followed by lowercase letters
    3. Words are separated by non-alphabetic characters
    4. There is at least one cased character in the string
    
    Examples:
    - "Title Case" → True
    - "Numpy Is Great" → True  
    - "numpy is great" → False
    - "NUMPY IS GREAT" → False
    - "" → False
    - "123" → False
-/
def istitle {n : Nat} (a : Vector String n) : Id (Vector Bool n) :=
  pure (a.map isTitlecased)

/-- Specification: numpy.strings.istitle returns a vector where each element indicates
    whether the corresponding string element is titlecased.
    
    Mathematical properties:
    1. Empty strings return False
    2. Strings with no alphabetic characters return False
    3. Strings where every word starts with uppercase followed by lowercase return True
    4. Words are defined as sequences of alphabetic characters separated by non-alphabetic characters
    5. At least one cased character must be present
-/
theorem istitle_spec {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    istitle a
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = isTitlecased (a.get i)⌝⦄ := by
  sorry

/-- Specification: Empty strings return False -/
theorem istitle_empty_string {n : Nat} (a : Vector String n) :
    ⦃⌜∀ i : Fin n, a.get i = ""⌝⦄
    istitle a
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = false⌝⦄ := by
  sorry

/-- Specification: Strings with no cased characters return False -/
theorem istitle_no_cased_chars {n : Nat} (a : Vector String n) :
    ⦃⌜∀ i : Fin n, a.get i ≠ "" ∧ (a.get i).toList.all (fun c => ¬c.isUpper ∧ ¬c.isLower)⌝⦄
    istitle a
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = false⌝⦄ := by
  sorry

/-- Specification: Proper title case strings return True -/
theorem istitle_proper_title_case {n : Nat} (a : Vector String n) :
    ⦃⌜∀ i : Fin n, isTitlecased (a.get i) = true⌝⦄
    istitle a
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = true⌝⦄ := by
  sorry

/-- Specification: Strings that are not title cased return False -/
theorem istitle_not_title_case {n : Nat} (a : Vector String n) :
    ⦃⌜∀ i : Fin n, isTitlecased (a.get i) = false⌝⦄
    istitle a
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = false⌝⦄ := by
  sorry

/-- Specification: The function is deterministic -/
theorem istitle_deterministic {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    istitle a
    ⦃⇓result1 => ⌜∀ result2 : Vector Bool n, 
      (∀ i : Fin n, result2.get i = isTitlecased (a.get i)) → 
      (∀ i : Fin n, result1.get i = result2.get i)⌝⦄ := by
  sorry