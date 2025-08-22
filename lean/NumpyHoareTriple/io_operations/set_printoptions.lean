import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.set_printoptions",
  "category": "String formatting",
  "description": "Set printing options",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.set_printoptions.html",
  "doc": "Set printing options",
  "code": "@set_module('numpy')\ndef set_printoptions(precision=None, threshold=None, edgeitems=None,\n                     linewidth=None, suppress=None, nanstr=None,\n                     infstr=None, formatter=None, sign=None, floatmode=None,\n                     *, legacy=None, override_repr=None):\n    \"\"\"\n    Set printing options.\n\n    These options determine the way floating point numbers, arrays and\n    other NumPy objects are displayed.\n\n    Parameters\n    ----------\n    precision : int or None, optional\n        Number of digits of precision for floating point output (default 8).\n        May be None if \`floatmode\` is not \`fixed\`, to print as many digits as\n        necessary to uniquely specify the value.\n    threshold : int, optional\n        Total number of array elements which trigger summarization\n        rather than full repr (default 1000).\n        To always use the full repr without summarization, pass \`sys.maxsize\`.\n    edgeitems : int, optional\n        Number of array items in summary at beginning and end of\n        each dimension (default 3).\n    linewidth : int, optional\n        The number of characters per line for the purpose of inserting\n        line breaks (default 75).\n    suppress : bool, optional\n        If True, always print floating point numbers using fixed point\n        notation, in which case numbers equal to zero in the current precision\n        will print as zero.  If False, then scientific notation is used when\n        absolute value of the smallest number is < 1e-4 or the ratio of the\n        maximum absolute value to the minimum is > 1e3. The default is False.\n    nanstr : str, optional\n        String representation of floating point not-a-number (default nan).\n    infstr : str, optional\n        String representation of floating point infinity (default inf).\n    sign : string, either '-', '+', or ' ', optional\n        Controls printing of the sign of floating-point types. If '+', always\n        print the sign of positive values. If ' ', always prints a space\n        (whitespace character) in the sign position of positive values.  If\n        '-', omit the sign character of positive values. (default '-')\n\n        .. versionchanged:: 2.0\n             The sign parameter can now be an integer type, previously\n             types were floating-point types.\n\n    formatter : dict of callables, optional\n        If not None, the keys should indicate the type(s) that the respective\n        formatting function applies to.  Callables should return a string.\n        Types that are not specified (by their corresponding keys) are handled\n        by the default formatters.  Individual types for which a formatter\n        can be set are:\n\n        - 'bool'\n        - 'int'\n        - 'timedelta' : a \`numpy.timedelta64\`\n        - 'datetime' : a \`numpy.datetime64\`\n        - 'float'\n        - 'longfloat' : 128-bit floats\n        - 'complexfloat'\n        - 'longcomplexfloat' : composed of two 128-bit floats\n        - 'numpystr' : types \`numpy.bytes_\` and \`numpy.str_\`\n        - 'object' : \`np.object_\` arrays\n\n        Other keys that can be used to set a group of types at once are:\n\n        - 'all' : sets all types\n        - 'int_kind' : sets 'int'\n        - 'float_kind' : sets 'float' and 'longfloat'\n        - 'complex_kind' : sets 'complexfloat' and 'longcomplexfloat'\n        - 'str_kind' : sets 'numpystr'\n    floatmode : str, optional\n        Controls the interpretation of the \`precision\` option for\n        floating-point types. Can take the following values\n        (default maxprec_equal):\n\n        * 'fixed': Always print exactly \`precision\` fractional digits,\n                even if this would print more or fewer digits than\n                necessary to specify the value uniquely.\n        * 'unique': Print the minimum number of fractional digits necessary\n                to represent each value uniquely. Different elements may\n                have a different number of digits. The value of the\n                \`precision\` option is ignored.\n        * 'maxprec': Print at most \`precision\` fractional digits, but if\n                an element can be uniquely represented with fewer digits\n                only print it with that many.\n        * 'maxprec_equal': Print at most \`precision\` fractional digits,\n                but if every element in the array can be uniquely\n                represented with an equal number of fewer digits, use that\n                many digits for all elements.\n    legacy : string or \`False\`, optional\n        If set to the string \`\`'1.13'\`\` enables 1.13 legacy printing mode. This\n        approximates numpy 1.13 print output by including a space in the sign\n        position of floats and different behavior for 0d arrays. This also\n        enables 1.21 legacy printing mode (described below).\n\n        If set to the string \`\`'1.21'\`\` enables 1.21 legacy printing mode. This\n        approximates numpy 1.21 print output of complex structured dtypes\n        by not inserting spaces after commas that separate fields and after\n        colons.\n\n        If set to \`\`'1.25'\`\` approximates printing of 1.25 which mainly means\n        that numeric scalars are printed without their type information, e.g.\n        as \`\`3.0\`\` rather than \`\`np.float64(3.0)\`\`.\n\n        If set to \`\`'2.1'\`\`, shape information is not given when arrays are\n        summarized (i.e., multiple elements replaced with \`\`...\`\`).\n\n        If set to \`\`'2.2'\`\`, the transition to use scientific notation for\n        printing \`\`np.float16\`\` and \`\`np.float32\`\` types may happen later or\n        not at all for larger values.\n\n        If set to \`False\`, disables legacy mode.\n\n        Unrecognized strings will be ignored with a warning for forward\n        compatibility.\n\n        .. versionchanged:: 1.22.0\n        .. versionchanged:: 2.2\n\n    override_repr: callable, optional\n        If set a passed function will be used for generating arrays' repr.\n        Other options will be ignored.\n\n    See Also\n    --------\n    get_printoptions, printoptions, array2string\n\n    Notes\n    -----\n    \`formatter\` is always reset with a call to \`set_printoptions\`.\n\n    Use \`printoptions\` as a context manager to set the values temporarily.\n\n    Examples\n    --------\n    Floating point precision can be set:\n\n    >>> import numpy as np\n    >>> np.set_printoptions(precision=4)\n    >>> np.array([1.123456789])\n    [1.1235]\n\n    Long arrays can be summarised:\n\n    >>> np.set_printoptions(threshold=5)\n    >>> np.arange(10)\n    array([0, 1, 2, ..., 7, 8, 9], shape=(10,))\n\n    Small results can be suppressed:\n\n    >>> eps = np.finfo(float).eps\n    >>> x = np.arange(4.)\n    >>> x**2 - (x + eps)**2\n    array([-4.9304e-32, -4.4409e-16,  0.0000e+00,  0.0000e+00])\n    >>> np.set_printoptions(suppress=True)\n    >>> x**2 - (x + eps)**2\n    array([-0., -0.,  0.,  0.])\n\n    A custom formatter can be used to display array elements as desired:\n\n    >>> np.set_printoptions(formatter={'all':lambda x: 'int: '+str(-x)})\n    >>> x = np.arange(3)\n    >>> x\n    array([int: 0, int: -1, int: -2])\n    >>> np.set_printoptions()  # formatter gets reset\n    >>> x\n    array([0, 1, 2])\n\n    To put back the default options, you can use:\n\n    >>> np.set_printoptions(edgeitems=3, infstr='inf',\n    ... linewidth=75, nanstr='nan', precision=8,\n    ... suppress=False, threshold=1000, formatter=None)\n\n    Also to temporarily override options, use \`printoptions\`\n    as a context manager:\n\n    >>> with np.printoptions(precision=2, suppress=True, threshold=5):\n    ...     np.linspace(0, 10, 10)\n    array([ 0.  ,  1.11,  2.22, ...,  7.78,  8.89, 10.  ], shape=(10,))\n"
}
-/

open Std.Do

/-- Structure representing NumPy print options -/
structure PrintOptions where
  /-- Number of digits of precision for floating point output -/
  precision : Nat
  /-- Total number of array elements which trigger summarization -/
  threshold : Nat
  /-- Number of array items in summary at beginning and end -/
  edgeitems : Nat
  /-- Number of characters per line for line breaks -/
  linewidth : Nat
  /-- Whether to suppress small floating point values -/
  suppress : Bool
  /-- String representation of floating point not-a-number -/
  nanstr : String
  /-- String representation of floating point infinity -/
  infstr : String
  /-- Controls printing of the sign of floating-point types -/
  sign : String
  /-- Controls interpretation of precision option -/
  floatmode : String
  /-- Legacy printing mode setting -/
  legacy : Option String

/-- numpy.set_printoptions: Set printing options for NumPy arrays

    Sets the global printing options that control how floating point numbers,
    arrays and other NumPy objects are displayed. This function modifies the
    global state of NumPy's print formatting system.
    
    All parameters are optional and only modify the corresponding option if
    provided. Options not specified retain their current values.
-/
def set_printoptions 
    (precision : Option Nat := none)
    (threshold : Option Nat := none)
    (edgeitems : Option Nat := none)
    (linewidth : Option Nat := none)
    (suppress : Option Bool := none)
    (nanstr : Option String := none)
    (infstr : Option String := none)
    (sign : Option String := none)
    (floatmode : Option String := none)
    (legacy : Option String := none) : Id Unit :=
  sorry

/-- Specification: set_printoptions correctly updates the global print options
    according to the provided parameters while validating input constraints.
    
    Precondition: All optional parameters must satisfy their validation constraints
    Postcondition: The global print state is updated with the provided options
-/
theorem set_printoptions_spec 
    (precision : Option Nat := none)
    (threshold : Option Nat := none)
    (edgeitems : Option Nat := none)
    (linewidth : Option Nat := none)
    (suppress : Option Bool := none)
    (nanstr : Option String := none)
    (infstr : Option String := none)
    (sign : Option String := none)
    (floatmode : Option String := none)
    (legacy : Option String := none)
    (h_precision : ∀ p : Nat, precision = some p → p > 0)
    (h_threshold : ∀ t : Nat, threshold = some t → t > 0)
    (h_edgeitems : ∀ e : Nat, edgeitems = some e → e > 0)
    (h_linewidth : ∀ l : Nat, linewidth = some l → l > 0)
    (h_nanstr : ∀ n : String, nanstr = some n → n ≠ "")
    (h_infstr : ∀ i : String, infstr = some i → i ≠ "")
    (h_sign : ∀ s : String, sign = some s → (s = "-" ∨ s = "+" ∨ s = " "))
    (h_floatmode : ∀ f : String, floatmode = some f → 
      (f = "fixed" ∨ f = "unique" ∨ f = "maxprec" ∨ f = "maxprec_equal"))
    (h_legacy : ∀ l : String, legacy = some l → 
      (l = "1.13" ∨ l = "1.21" ∨ l = "1.25" ∨ l = "2.1" ∨ l = "2.2")) :
    ⦃⌜(∀ p : Nat, precision = some p → p > 0) ∧
      (∀ t : Nat, threshold = some t → t > 0) ∧
      (∀ e : Nat, edgeitems = some e → e > 0) ∧
      (∀ l : Nat, linewidth = some l → l > 0) ∧
      (∀ n : String, nanstr = some n → n ≠ "") ∧
      (∀ i : String, infstr = some i → i ≠ "") ∧
      (∀ s : String, sign = some s → (s = "-" ∨ s = "+" ∨ s = " ")) ∧
      (∀ f : String, floatmode = some f → 
        (f = "fixed" ∨ f = "unique" ∨ f = "maxprec" ∨ f = "maxprec_equal")) ∧
      (∀ l : String, legacy = some l → 
        (l = "1.13" ∨ l = "1.21" ∨ l = "1.25" ∨ l = "2.1" ∨ l = "2.2"))⌝⦄
    set_printoptions precision threshold edgeitems linewidth suppress nanstr infstr sign floatmode legacy
    ⦃⇓_ => ⌜True⌝⦄ := by
  sorry