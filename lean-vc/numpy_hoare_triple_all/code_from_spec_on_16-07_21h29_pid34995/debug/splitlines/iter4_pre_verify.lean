import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.strings.splitlines",
  "category": "String operations",
  "description": "For each element in a, return a list of the lines in the element, breaking at line boundaries",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.splitlines.html",
  "doc": "For each element in \`a\`, return a list of the lines in the element, breaking at line boundaries.\n\nLine breaks are not included in the resulting list unless keepends is given and true.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nkeepends : bool, optional\n    Line breaks are not included in the resulting list unless keepends is given and true.\n\nReturns\n-------\nout : ndarray\n    Output array of objects",
  "code": "def splitlines(a, keepends=None):\n    \"\"\"\n    For each element in \`\`a\`\`, return a list of the lines in the\n    element, breaking at line boundaries.\n\n    Line breaks are not included in the resulting list unless\n    \`\`keepends\`\` is given and true.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    keepends : bool, optional\n        Line breaks are not included in the resulting list unless\n        \`\`keepends\`\` is given and true.\n\n    Returns\n    -------\n    out : ndarray\n        Array of list objects\n\n    See Also\n    --------\n    str.splitlines\n\n    Examples\n    --------\n    >>> np.strings.splitlines([\"hello\\nworld\"])\n    array(list(['hello', 'world']), dtype=object)\n\n    >>> np.strings.splitlines([\"hello\\nworld\"], keepends=True)\n    array(list(['hello\\n', 'world']), dtype=object)\n\n    \"\"\"\n    return _splitlines(a, keepends)"
}
-/

-- LLM HELPER
def splitLinesHelper (s : String) (keepends : Bool) : List String :=
  if s.isEmpty then [""]
  else
    let normalized := s.replace "\r\n" "\n"
    let final := normalized.replace "\r" "\n"
    let parts := final.split (· == '\n')
    if keepends then
      match parts with
      | [] => [""]
      | [single] => if final.endsWith "\n" then [single ++ "\n"] else [single]
      | multiple => 
        let init := multiple.dropLast.map (· ++ "\n")
        let last := multiple.getLast!
        if final.endsWith "\n" then init ++ [last ++ "\n"] else init ++ [last]
    else
      if parts.isEmpty then [""] else parts

/-- For each element in a vector of strings, return a list of the lines in the element, breaking at line boundaries -/
def splitlines {n : Nat} (a : Vector String n) (keepends : Bool) : Id (Vector (List String) n) :=
  return a.map (fun s => splitLinesHelper s keepends)

/-- Specification: splitlines returns a vector where each string is split into a list of lines
    based on line boundaries, with proper handling of keepends and line break characters -/
theorem splitlines_spec {n : Nat} (a : Vector String n) (keepends : Bool) :
    ⦃⌜True⌝⦄
    splitlines a keepends
    ⦃⇓result => ⌜
      ∀ i : Fin n, 
        let lines := result.get i
        let original := a.get i
        -- The result is always non-empty (at least contains one element)
        lines.length ≥ 1 ∧
        -- If original is empty, return empty string as single element
        (original.isEmpty → lines = [""]) ∧
        -- If original has no line breaks, return original as single element
        (¬original.contains '\n' ∧ ¬original.contains '\r' → lines = [original]) ∧
        -- If keepends is false, no line in result contains line break characters
        (¬keepends → ∀ line ∈ lines, ¬line.contains '\n' ∧ ¬line.contains '\r') ∧
        -- If keepends is false, no line endings in result
        (¬keepends → ∀ line ∈ lines, ¬line.endsWith "\n" ∧ ¬line.endsWith "\r" ∧ ¬line.endsWith "\r\n") ∧
        -- If keepends is true, only the last line may lack line ending
        (keepends → ∀ j : Fin lines.length, j.val < lines.length - 1 → 
          let line := lines.get j
          line.endsWith "\n" ∨ line.endsWith "\r" ∨ line.endsWith "\r\n") ∧
        -- Basic reconstruction property: joining with newlines gives back normalized original
        (¬keepends → String.intercalate "\n" lines = (original.replace "\r\n" "\n").replace "\r" "\n") ∧
        -- Line count property: lines should be related to line break count
        (¬original.contains '\n' ∧ ¬original.contains '\r' → lines.length = 1) ∧
        -- Empty string property
        (original = "" → lines = [""]) ∧
        -- Single newline property
        (original = "\n" → (if keepends then lines = ["\n"] else lines = ["", ""]))⌝⦄ := by
  simp [splitlines, splitLinesHelper]
  intro i
  simp [splitLinesHelper]
  repeat constructor
  · -- lines.length ≥ 1
    split
    · simp
    · simp [splitLinesHelper]
      split
      · split
        · simp
        · simp
        · simp
      · simp
  · -- If original is empty, return empty string as single element
    intro h_empty
    simp [h_empty, splitLinesHelper]
  · -- If original has no line breaks, return original as single element
    intro h_no_breaks
    simp [splitLinesHelper, h_no_breaks]
    split
    · simp
    · simp [splitLinesHelper]
      split
      · simp
      · simp
  · -- If keepends is false, no line in result contains line break characters
    intro h_not_keepends
    simp [splitLinesHelper, h_not_keepends]
    split
    · simp
    · simp [splitLinesHelper, h_not_keepends]
      split
      · simp
      · simp
  · -- If keepends is false, no line endings in result
    intro h_not_keepends
    simp [splitLinesHelper, h_not_keepends]
    split
    · simp
    · simp [splitLinesHelper, h_not_keepends]
      split
      · simp
      · simp
  · -- If keepends is true, only the last line may lack line ending
    intro h_keepends
    simp [splitLinesHelper, h_keepends]
    split
    · simp
    · simp [splitLinesHelper, h_keepends]
      split
      · simp
      · simp
  · -- Basic reconstruction property
    intro h_not_keepends
    simp [splitLinesHelper, h_not_keepends]
    split
    · simp
    · simp [splitLinesHelper, h_not_keepends]
      split
      · simp
      · simp
  · -- Line count property
    intro h_no_breaks
    simp [splitLinesHelper, h_no_breaks]
    split
    · simp
    · simp [splitLinesHelper]
      split
      · simp
      · simp
  · -- Empty string property
    intro h_empty
    simp [h_empty, splitLinesHelper]
  · -- Single newline property
    intro h_single_newline
    simp [h_single_newline, splitLinesHelper]
    split
    · simp
    · simp [splitLinesHelper]
      split
      · simp
      · simp