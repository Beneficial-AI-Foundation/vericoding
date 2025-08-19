import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.typename",
  "category": "Miscellaneous Type Utilities",
  "description": "Return a description for the given data type code",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.typename.html",
  "doc": "Return a description for the given data type code.\n\nParameters\n----------\nchar : str\n    Data type code.\n\nReturns\n-------\nout : str\n    Description of the input data type code.\n\nExamples\n--------\n>>> typechars = ['S1', '?', 'B', 'D', 'G', 'F', 'I', 'H', 'L', 'O', 'Q',\n...              'S', 'U', 'V', 'b', 'd', 'g', 'f', 'i', 'h', 'l', 'q']\n>>> for typechar in typechars:\n...     print(typechar, ' : ', np.typename(typechar))\n...\nS1  :  character\n?  :  bool\nB  :  unsigned char\nD  :  complex double precision\nG  :  complex long double precision\nF  :  complex single precision\nI  :  unsigned integer\nH  :  unsigned short\nL  :  unsigned long integer\nO  :  object\nQ  :  unsigned long long integer\nS  :  character\nU  :  unicode\nV  :  void\nb  :  signed char\nd  :  double precision\ng  :  long precision\nf  :  single precision\ni  :  integer\nh  :  short\nl  :  long integer\nq  :  long long integer",
  "code": "# C implementation for performance\n# Return a description for the given data type code\n#\n# This function is implemented in C as part of NumPy's core multiarray module.\n# The C implementation provides:\n# - Optimized memory access patterns\n# - Efficient array manipulation\n# - Low-level control over data layout\n# - Integration with NumPy's array object internals\n#\n# Source: C implementation in multiarray module"
}
-/

/-- Return a description for the given data type code -/
def typename (char : String) : Id String :=
  match char with
  | "S1" => "character"
  | "?" => "bool"
  | "B" => "unsigned char"
  | "D" => "complex double precision"
  | "G" => "complex long double precision"
  | "F" => "complex single precision"
  | "I" => "unsigned integer"
  | "H" => "unsigned short"
  | "L" => "unsigned long integer"
  | "O" => "object"
  | "Q" => "unsigned long long integer"
  | "S" => "character"
  | "U" => "unicode"
  | "V" => "void"
  | "b" => "signed char"
  | "d" => "double precision"
  | "g" => "long precision"
  | "f" => "single precision"
  | "i" => "integer"
  | "h" => "short"
  | "l" => "long integer"
  | "q" => "long long integer"
  | _ => "unknown type"

/-- Specification: typename maps data type codes to their descriptions -/
theorem typename_spec (char : String) :
    ⦃⌜True⌝⦄
    typename char
    ⦃⇓result => ⌜
      -- Known type code mappings from NumPy documentation
      (char = "S1" → result = "character") ∧
      (char = "?" → result = "bool") ∧
      (char = "B" → result = "unsigned char") ∧
      (char = "D" → result = "complex double precision") ∧
      (char = "G" → result = "complex long double precision") ∧
      (char = "F" → result = "complex single precision") ∧
      (char = "I" → result = "unsigned integer") ∧
      (char = "H" → result = "unsigned short") ∧
      (char = "L" → result = "unsigned long integer") ∧
      (char = "O" → result = "object") ∧
      (char = "Q" → result = "unsigned long long integer") ∧
      (char = "S" → result = "character") ∧
      (char = "U" → result = "unicode") ∧
      (char = "V" → result = "void") ∧
      (char = "b" → result = "signed char") ∧
      (char = "d" → result = "double precision") ∧
      (char = "g" → result = "long precision") ∧
      (char = "f" → result = "single precision") ∧
      (char = "i" → result = "integer") ∧
      (char = "h" → result = "short") ∧
      (char = "l" → result = "long integer") ∧
      (char = "q" → result = "long long integer") ∧
      -- For unknown type codes, the function should return some default description
      (char ∉ ["S1", "?", "B", "D", "G", "F", "I", "H", "L", "O", "Q", 
               "S", "U", "V", "b", "d", "g", "f", "i", "h", "l", "q"] → 
       result = "unknown type" ∨ result = char)
    ⌝⦄ := by
  unfold typename
  split <;> {
    simp [Triple.wpReturn]
    constructor
    · intro h
      rfl
    · intro h
      rfl
    · intro h
      rfl
    · intro h
      rfl
    · intro h
      rfl
    · intro h
      rfl
    · intro h
      rfl
    · intro h
      rfl
    · intro h
      rfl
    · intro h
      rfl
    · intro h
      rfl
    · intro h
      rfl
    · intro h
      rfl
    · intro h
      rfl
    · intro h
      rfl
    · intro h
      rfl
    · intro h
      rfl
    · intro h
      rfl
    · intro h
      rfl
    · intro h
      rfl
    · intro h
      rfl
    · intro h
      rfl
    · intro h
      left
      rfl
  }