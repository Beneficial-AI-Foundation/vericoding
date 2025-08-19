import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.testing.rundocs",
  "category": "Test Running",
  "description": "Run doctests found in the given file",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.testing.rundocs.html",
  "doc": "Run doctests found in the given file.\n\nBy default \`rundocs\` raises an AssertionError on failure.",
  "code": "def rundocs(filename=None, raise_on_error=True):\n    \"\"\"\n    Run doctests found in the given file.\n\n    By default \`rundocs\` raises an AssertionError on failure.\n\n    Parameters\n    ----------\n    filename : str\n        The path to the file for which the doctests are run.\n    raise_on_error : bool\n        Whether to raise an AssertionError when a doctest fails. Default is\n        True.\n\n    Notes\n    -----\n    The doctests can be run by the user/developer by adding the \`\`doctests\`\`\n    argument to the \`\`test()\`\` call. For example, to run all tests (including\n    doctests) for \`numpy.lib\`::\n\n        >>> np.lib.test(doctests=True)  # doctest: +SKIP\n    \"\"\"\n    from numpy._core import arange\n    import doctest\n\n    if filename is None:\n        f = sys._getframe(1)\n        filename = f.f_globals['__file__']\n    name = os.path.splitext(os.path.basename(filename))[0]\n    m = sys.modules[name]?\n\n    if m is None:\n        raise ImportError(name)\n\n    tests = doctest.DocTestFinder().find(m)\n    runner = doctest.DocTestRunner(verbose=True)\n\n    msg = \"Some doctests failed:\\n\"\n    had_failure = False\n\n    for test in tests:\n        failures, tries = runner.run(test)\n\n        if failures > 0:\n            had_failure = True\n            msg += \"\\n\".join(\n                [test.name, \"-\"*70, runner.failures[0][0].getvalue()])\n\n    if had_failure and raise_on_error:\n        raise AssertionError(msg)"
}
-/

open Std.Do

/-- Result of running doctests, containing success status and error message -/
structure DocTestResult where
  /-- Whether all doctests passed -/
  success : Bool
  /-- Error message if tests failed -/
  error_message : String

-- LLM HELPER
/-- Simulate running doctests for a file -/
def runDoctestsForFile (filename : String) : Bool :=
  -- Simplified simulation: return true for valid filenames
  filename.length > 0 && filename.endsWith ".py"

/-- Run doctests found in the given file -/
def rundocs (filename : Option String) (raise_on_error : Bool := true) : Id DocTestResult :=
  match filename with
  | none => 
    -- Simulate automatic filename detection
    let defaultFile := "current_module.py"
    let testsPass := runDoctestsForFile defaultFile
    if testsPass then
      { success := true, error_message := "" }
    else
      { success := false, error_message := "Some doctests failed in " ++ defaultFile }
  | some file =>
    let testsPass := runDoctestsForFile file
    if testsPass then
      { success := true, error_message := "" }
    else
      { success := false, error_message := "Some doctests failed in " ++ file }

/-- Specification: rundocs processes a file and returns test results.
    Mathematical properties:
    1. The function returns a result with success status and error message
    2. If tests pass, success is true and error message is empty
    3. If tests fail and raise_on_error is true, success is false and error message is non-empty
    4. The function handles both explicit filenames and automatic detection -/
theorem rundocs_spec (filename : Option String) (raise_on_error : Bool) :
    ⦃⌜True⌝⦄
    rundocs filename raise_on_error
    ⦃⇓result => ⌜-- Core property: function returns valid result structure
                 (result.success = true ∨ result.success = false) ∧
                 -- If tests pass, success is true and error message is empty
                 (result.success = true → result.error_message = "") ∧
                 -- If tests fail and raise_on_error is true, success is false and error message is non-empty
                 (result.success = false ∧ raise_on_error → result.error_message ≠ "") ∧
                 -- If raise_on_error is false, the function can still indicate failure but won't raise
                 (¬raise_on_error → (result.success = true ∨ result.success = false)) ∧
                 -- Result is deterministic for the same input
                 True⌝⦄ := by
  unfold rundocs
  simp only [Id.bind_eq]
  intro
  split
  · -- Case: filename is none
    simp only [runDoctestsForFile, String.length_append]
    split
    · -- Tests pass
      simp only [and_true, true_or, implies_true_iff, not_false_eq_true]
      constructor
      · left; rfl
      · constructor
        · intro; rfl
        · constructor
          · intro h; exact h.1
          · constructor
            · intro; left; rfl
            · trivial
    · -- Tests fail
      simp only [and_true, false_or, not_true_eq_false, not_false_eq_true]
      constructor
      · right; rfl
      · constructor
        · intro h; contradiction
        · constructor
          · intro h; simp only [ne_eq, String.append_ne_empty_iff]
            left; exact String.nonempty_of_ne_empty (fun h => by simp at h)
          · constructor
            · intro; right; rfl
            · trivial
  · -- Case: filename is some file
    simp only [runDoctestsForFile]
    split
    · -- Tests pass
      simp only [and_true, true_or, implies_true_iff, not_false_eq_true]
      constructor
      · left; rfl
      · constructor
        · intro; rfl
        · constructor
          · intro h; exact h.1
          · constructor
            · intro; left; rfl
            · trivial
    · -- Tests fail
      simp only [and_true, false_or, not_true_eq_false, not_false_eq_true]
      constructor
      · right; rfl
      · constructor
        · intro h; contradiction
        · constructor
          · intro h; simp only [ne_eq, String.append_ne_empty_iff]
            left; exact String.nonempty_of_ne_empty (fun h => by simp at h)
          · constructor
            · intro; right; rfl
            · trivial