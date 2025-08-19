import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Print options structure to represent configuration -/
structure PrintOptions where
  /-- Number of digits of precision for floating point output -/
  precision : Nat
  /-- Total number of array elements which trigger summarization -/
  threshold : Nat
  /-- Number of array items in summary at beginning and end -/
  edgeitems : Nat
  /-- Number of characters per line for inserting line breaks -/
  linewidth : Nat
  /-- Whether to suppress small floating point values -/
  suppress : Bool
  /-- String representation of floating point NaN -/
  nanstr : String
  /-- String representation of floating point infinity -/
  infstr : String

/-- Context manager result representing the temporary state change -/
structure PrintOptionsContext where
  /-- The original print options before the context change -/
  old_options : PrintOptions
  /-- The new print options active within the context -/
  new_options : PrintOptions

-- LLM HELPER
def default_print_options : PrintOptions :=
  { precision := 8
  , threshold := 1000
  , edgeitems := 3
  , linewidth := 75
  , suppress := false
  , nanstr := "nan"
  , infstr := "inf" }

/-- numpy.printoptions: Context manager for setting print options.

    Creates a context manager that temporarily sets print options and restores
    the original options afterward. This allows for local formatting changes
    without affecting global state.

    The context manager returns the current print options that are active
    within the context.
-/
def numpy_printoptions (new_opts : PrintOptions) : Id PrintOptionsContext :=
  { old_options := default_print_options
  , new_options := new_opts }

-- LLM HELPER
instance : DecidableEq PrintOptions := by
  unfold DecidableEq
  intro a b
  cases a with
  | mk p1 t1 e1 l1 s1 n1 i1 =>
    cases b with
    | mk p2 t2 e2 l2 s2 n2 i2 =>
      if h1 : p1 = p2 then
        if h2 : t1 = t2 then
          if h3 : e1 = e2 then
            if h4 : l1 = l2 then
              if h5 : s1 = s2 then
                if h6 : n1 = n2 then
                  if h7 : i1 = i2 then
                    exact isTrue (by simp [h1, h2, h3, h4, h5, h6, h7])
                  else
                    exact isFalse (by simp [h7])
                else
                  exact isFalse (by simp [h6])
              else
                exact isFalse (by simp [h5])
            else
              exact isFalse (by simp [h4])
          else
            exact isFalse (by simp [h3])
        else
          exact isFalse (by simp [h2])
      else
        exact isFalse (by simp [h1])

/-- Specification: numpy.printoptions creates a context with temporary print options.

    Precondition: Valid print options are provided
    Postcondition: Returns a context that contains both old and new options,
                   where the new options are the ones that would be active
                   within the context
-/
theorem numpy_printoptions_spec (new_opts : PrintOptions) :
    ⦃⌜True⌝⦄
    numpy_printoptions new_opts
    ⦃⇓context => ⌜context.new_options = new_opts ∧ 
                   context.old_options ≠ context.new_options⌝⦄ := by
  simp [numpy_printoptions, default_print_options]
  exact ⟨rfl, fun h => by cases h; simp⟩