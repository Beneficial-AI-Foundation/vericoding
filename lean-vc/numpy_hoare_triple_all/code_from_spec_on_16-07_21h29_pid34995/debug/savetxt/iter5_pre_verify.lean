import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.savetxt",
  "category": "Text file I/O",
  "description": "Save an array to a text file",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.savetxt.html",
  "doc": "Save an array to a text file",
  "code": "@array_function_dispatch(_savetxt_dispatcher)\ndef savetxt(fname, X, fmt='%.18e', delimiter=' ', newline='\\n', header='',\n            footer='', comments='# ', encoding=None):\n    \"\"\"\n    Save an array to a text file.\n\n    Parameters\n    ----------\n    fname : filename, file handle or pathlib.Path\n        If the filename ends in \`\`.gz\`\`, the file is automatically saved in\n        compressed gzip format.  \`loadtxt\` understands gzipped files\n        transparently.\n    X : 1D or 2D array_like\n        Data to be saved to a text file.\n    fmt : str or sequence of strs, optional\n        A single format (%10.5f), a sequence of formats, or a\n        multi-format string, e.g. 'Iteration %d -- %10.5f', in which\n        case \`delimiter\` is ignored. For complex \`X\`, the legal options\n        for \`fmt\` are:\n\n        * a single specifier, \`\`fmt='%.4e'\`\`, resulting in numbers formatted\n          like \`\`' (%s+%sj)' % (fmt, fmt)\`\`\n        * a full string specifying every real and imaginary part, e.g.\n          \`\`' %.4e %+.4ej %.4e %+.4ej %.4e %+.4ej'\`\` for 3 columns\n        * a list of specifiers, one per column - in this case, the real\n          and imaginary part must have separate specifiers,\n          e.g. \`\`['%.3e + %.3ej', '(%.15e%+.15ej)']\`\` for 2 columns\n    delimiter : str, optional\n        String or character separating columns.\n    newline : str, optional\n        String or character separating lines.\n    header : str, optional\n        String that will be written at the beginning of the file.\n    footer : str, optional\n        String that will be written at the end of the file.\n    comments : str, optional\n        String that will be prepended to the \`\`header\`\` and \`\`footer\`\` strings,\n        to mark them as comments. Default: '# ',  as expected by e.g.\n        \`\`numpy.loadtxt\`\`.\n    encoding : {None, str}, optional\n        Encoding used to encode the outputfile. Does not apply to output\n        streams. If the encoding is something other than 'bytes' or 'latin1'\n        you will not be able to load the file in NumPy versions < 1.14. Default\n        is 'latin1'.\n\n    See Also\n    --------\n    save : Save an array to a binary file in NumPy \`\`.npy\`\` format\n    savez : Save several arrays into an uncompressed \`\`.npz\`\` archive\n    savez_compressed : Save several arrays into a compressed \`\`.npz\`\` archive\n\n    Notes\n    -----\n    Further explanation of the \`fmt\` parameter\n    (\`\`%[flag]width[.precision]specifier\`\`):\n\n    flags:\n        \`\`-\`\` : left justify\n\n        \`\`+\`\` : Forces to precede result with + or -.\n\n        \`\`0\`\` : Left pad the number with zeros instead of space (see width).\n\n    width:\n        Minimum number of characters to be printed. The value is not truncated\n        if it has more characters.\n\n    precision:\n        - For integer specifiers (eg. \`\`d,i,o,x\`\`), the minimum number of\n          digits.\n        - For \`\`e, E\`\` and \`\`f\`\` specifiers, the number of digits to print\n          after the decimal point.\n        - For \`\`g\`\` and \`\`G\`\`, the maximum number of significant digits.\n        - For \`\`s\`\`, the maximum number of characters.\n\n    specifiers:\n        \`\`c\`\` : character\n\n        \`\`d\`\` or \`\`i\`\` : signed decimal integer\n\n        \`\`e\`\` or \`\`E\`\` : scientific notation with \`\`e\`\` or \`\`E\`\`.\n\n        \`\`f\`\` : decimal floating point\n\n        \`\`g,G\`\` : use the shorter of \`\`e,E\`\` or \`\`f\`\`\n\n        \`\`o\`\` : signed octal\n\n        \`\`s\`\` : string of characters\n\n        \`\`u\`\` : unsigned decimal integer\n\n        \`\`x,X\`\` : unsigned hexadecimal integer\n\n    This explanation of \`\`fmt\`\` is not complete, for an exhaustive\n    specification see [1]_.\n\n    References\n    ----------\n    .. [1] \`Format Specification Mini-Language\n           <https://docs.python.org/library/string.html#format-specification-mini-language>\`_,\n           Python Documentation.\n\n    Examples\n    --------\n    >>> import numpy as np\n    >>> x = y = z = np.arange(0.0,5.0,1.0)\n    >>> np.savetxt('test.out', x, delimiter=',')   # X is an array\n    >>> np.savetxt('test.out', (x,y,z))   # x,y,z equal sized 1D arrays\n    >>> np.savetxt('test.out', x, fmt='%1.4e')   # use exponential notation"
}
-/

/-- Helper function to format a float according to a format string -/
def formatFloat (val : Float) (_ : String) : String := toString val

/-- Helper function to join a list of strings with a delimiter -/
def joinStrings (strings : List String) (delimiter : String) : String := 
  match strings with
  | [] => ""
  | [s] => s
  | s :: rest => s ++ delimiter ++ joinStrings rest delimiter

-- LLM HELPER
def vectorToList {n : Nat} (vec : Vector Float n) : List Float :=
  List.range n |>.map (fun i => vec.get ⟨i, by simp [List.length_range]⟩)

/-- Save an array to a text file with specified formatting options.
    This function converts the vector data into a formatted string representation
    that can be written to a file. The delimiter separates elements, and the
    format string controls the numeric representation of each element. -/
def savetxt {n : Nat} (arr : Vector Float n) (_ : String) (delimiter : String := " ") (fmt : String := "%.18e") : Id String :=
  let values := vectorToList arr
  let formatted_values := values.map (fun v => formatFloat v fmt)
  joinStrings formatted_values delimiter

-- LLM HELPER
lemma list_range_nonempty {n : Nat} (h : n > 0) : List.range n ≠ [] := by
  rw [List.ne_nil_iff_length_pos]
  rw [List.length_range]
  exact h

-- LLM HELPER
lemma toString_nonempty (f : Float) : (toString f).length > 0 := by
  have h : toString f ≠ "" := Float.toString_ne_empty f
  rw [String.length_pos]
  exact h

-- LLM HELPER  
lemma Float.toString_ne_empty (f : Float) : f.toString ≠ "" := by
  simp [Float.toString]

-- LLM HELPER
lemma List.cons_head!_tail {α : Type*} (l : List α) (h : l ≠ []) : l = l.head! :: l.tail :=
  match l with
  | [] => by contradiction
  | a :: as => by simp [List.head!, List.tail]

/-- Specification: savetxt creates a text representation of the array that preserves
    the original data values and uses the specified formatting options.
    
    The function should:
    1. Format each element according to the format string
    2. Separate elements with the specified delimiter
    3. Preserve the numerical values (within format precision)
    4. Generate output that can be read back by loadtxt
    
    Mathematical properties:
    - The output string contains exactly n formatted numbers
    - Each number is formatted according to the format string
    - Numbers are separated by the delimiter
    - The original values are preserved within the precision of the format -/
theorem savetxt_spec {n : Nat} (arr : Vector Float n) (filename : String) (delimiter : String) (fmt : String) :
    ⦃⌜filename.length > 0 ∧ delimiter.length > 0 ∧ fmt.length > 0⌝⦄
    savetxt arr filename delimiter fmt
    ⦃⇓result => ⌜
      -- Result is a non-empty string when array is non-empty
      (n > 0 → result.length > 0) ∧
      -- For empty arrays, result is empty string
      (n = 0 → result = "") ∧
      -- Result contains formatted representations of the array data
      (∃ formatted_values : List String, 
        formatted_values.length = n ∧
        result = joinStrings formatted_values delimiter) ∧
      -- Each element is formatted according to the format specification
      (∀ i : Fin n, ∃ formatted_val : String, 
        formatted_val = formatFloat (arr.get i) fmt)
    ⌝⦄ := by
  unfold savetxt
  simp only [Triple.pure_triple]
  intro h
  constructor
  · intro hn
    by_cases h' : n = 0
    · subst h'
      simp at hn
    · simp [vectorToList]
      have : List.range n ≠ [] := list_range_nonempty (Nat.pos_of_ne_zero h')
      have this_eq : List.range n = (List.range n).head! :: (List.range n).tail := 
        List.cons_head!_tail (List.range n) this
      simp [joinStrings]
      cases' (List.range n) with head tail
      · contradiction
      · simp [joinStrings]
        rw [String.length_append]
        simp [formatFloat]
        have : (toString (arr.get ⟨head, by simp [List.mem_range]⟩)).length > 0 := toString_nonempty _
        omega
  constructor
  · intro hn
    subst hn
    simp [vectorToList, joinStrings]
    rfl
  constructor
  · use (vectorToList arr).map (fun v => formatFloat v fmt)
    constructor
    · simp [vectorToList]
    · rfl
  · intro i
    use formatFloat (arr.get i) fmt
    rfl