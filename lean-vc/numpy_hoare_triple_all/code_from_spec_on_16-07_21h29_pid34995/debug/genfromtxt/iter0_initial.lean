import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.genfromtxt",
  "category": "Text file I/O",
  "description": "Load data from a text file, with missing values handled as specified",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.genfromtxt.html",
  "doc": "Load data from a text file, with missing values handled as specified",
  "code": "@finalize_array_function_like\n@set_module('numpy')\ndef genfromtxt(fname, dtype=float, comments='#', delimiter=None,\n               skip_header=0, skip_footer=0, converters=None,\n               missing_values=None, filling_values=None, usecols=None,\n               names=None, excludelist=None,\n               deletechars=''.join(sorted(NameValidator.defaultdeletechars)),  # noqa: B008\n               replace_space='_', autostrip=False, case_sensitive=True,\n               defaultfmt=\"f%i\", unpack=None, usemask=False, loose=True,\n               invalid_raise=True, max_rows=None, encoding=None,\n               *, ndmin=0, like=None):\n    \"\"\"\n    Load data from a text file, with missing values handled as specified.\n\n    Each line past the first \`skip_header\` lines is split at the \`delimiter\`\n    character, and characters following the \`comments\` character are discarded.\n\n    Parameters\n    ----------\n    fname : file, str, pathlib.Path, list of str, generator\n        File, filename, list, or generator to read.  If the filename\n        extension is \`\`.gz\`\` or \`\`.bz2\`\`, the file is first decompressed. Note\n        that generators must return bytes or strings. The strings\n        in a list or produced by a generator are treated as lines.\n    dtype : dtype, optional\n        Data type of the resulting array.\n        If None, the dtypes will be determined by the contents of each\n        column, individually.\n    comments : str, optional\n        The character used to indicate the start of a comment.\n        All the characters occurring on a line after a comment are discarded.\n    delimiter : str, int, or sequence, optional\n        The string used to separate values.  By default, any consecutive\n        whitespaces act as delimiter.  An integer or sequence of integers\n        can also be provided as width(s) of each field.\n    skiprows : int, optional\n        \`skiprows\` was removed in numpy 1.10. Please use \`skip_header\` instead.\n    skip_header : int, optional\n        The number of lines to skip at the beginning of the file.\n    skip_footer : int, optional\n        The number of lines to skip at the end of the file.\n    converters : variable, optional\n        The set of functions that convert the data of a column to a value.\n        The converters can also be used to provide a default value\n        for missing data: \`\`converters = {3: lambda s: float(s or 0)}\`\`.\n    missing : variable, optional\n        \`missing\` was removed in numpy 1.10. Please use \`missing_values\`\n        instead.\n    missing_values : variable, optional\n        The set of strings corresponding to missing data.\n    filling_values : variable, optional\n        The set of values to be used as default when the data are missing.\n    usecols : sequence, optional\n        Which columns to read, with 0 being the first.  For example,\n        \`\`usecols = (1, 4, 5)\`\` will extract the 2nd, 5th and 6th columns.\n    names : {None, True, str, sequence}, optional\n        If \`names\` is True, the field names are read from the first line after\n        the first \`skip_header\` lines. This line can optionally be preceded\n        by a comment delimiter. Any content before the comment delimiter is\n        discarded. If \`names\` is a sequence or a single-string of\n        comma-separated names, the names will be used to define the field\n        names in a structured dtype. If \`names\` is None, the names of the\n        dtype fields will be used, if any.\n    excludelist : sequence, optional\n        A list of names to exclude. This list is appended to the default list\n        ['return','file','print']. Excluded names are appended with an\n        underscore: for example, \`file\` would become \`file_\`.\n    deletechars : str, optional\n        A string combining invalid characters that must be deleted from the\n        names.\n    defaultfmt : str, optional\n        A format used to define default field names, such as \"f%i\" or \"f_%02i\".\n    autostrip : bool, optional\n        Whether to automatically strip white spaces from the variables.\n    replace_space : char, optional\n        Character(s) used in replacement of white spaces in the variable\n        names. By default, use a '_'.\n    case_sensitive : {True, False, 'upper', 'lower'}, optional\n        If True, field names are case sensitive.\n        If False or 'upper', field names are converted to upper case.\n        If 'lower', field names are converted to lower case.\n    unpack : bool, optional\n        If True, the returned array is transposed, so that arguments may be\n        unpacked using \`\`x, y, z = genfromtxt(...)\`\`.  When used with a\n        structured data-type, arrays are returned for each field.\n        Default is False.\n    usemask : bool, optional\n        If True, return a masked array.\n        If False, return a regular array.\n    loose : bool, optional\n        If True, do not raise errors for invalid values.\n    invalid_raise : bool, optional\n        If True, an exception is raised if an inconsistency is detected in the\n        number of columns.\n        If False, a warning is emitted and the offending lines are skipped.\n    max_rows : int,  optional\n        The maximum number of rows to read. Must not be used with skip_footer\n        at the same time.  If given, the value must be at least 1. Default is\n        to read the entire file.\n    encoding : str, optional\n        Encoding used to decode the inputfile. Does not apply when \`fname\`\n        is a file object. The special value 'bytes' enables backward\n        compatibility workarounds that ensure that you receive byte arrays\n        when possible and passes latin1 encoded strings to converters.\n        Override this value to receive unicode arrays and pass strings\n        as input to converters.  If set to None the system default is used.\n        The default value is 'bytes'.\n\n        .. versionchanged:: 2.0\n            Before NumPy 2, the default was \`\`'bytes'\`\` for Python 2\n            compatibility. The default is now \`\`None\`\`.\n\n    ndmin : int, optional\n        Same parameter as \`loadtxt\`\n\n        .. versionadded:: 1.23.0\n    ${ARRAY_FUNCTION_LIKE}\n\n        .. versionadded:: 1.20.0\n\n    Returns\n    -------\n    out : ndarray\n        Data read from the text file. If \`usemask\` is True, this is a\n        masked array.\n\n    See Also\n    --------\n    numpy.loadtxt : equivalent function when no data is missing.\n\n    Notes\n    -----\n    * When spaces are used as delimiters, or when no delimiter has been given\n      as input, there should not be any missing data between two fields.\n    * When variables are named (either by a flexible dtype or with a \`names\`\n      sequence), there must not be any header in the file (else a ValueError\n      exception is raised).\n    * Individual values are not stripped of spaces by default.\n      When using a custom converter, make sure the function does remove spaces.\n    * Custom converters may receive unexpected values due to dtype\n      discovery.\n\n    References\n    ----------\n    .. [1] NumPy User Guide, section \`I/O with NumPy\n           <https://docs.scipy.org/doc/numpy/user/basics.io.genfromtxt.html>\`_.\n\n    Examples\n    --------\n    >>> from io import StringIO\n    >>> import numpy as np\n\n    Comma delimited file with mixed dtype\n\n    >>> s = StringIO(\"1,1.3,abcde\")\n    >>> data = np.genfromtxt(s, dtype=[('myint','i8'),('myfloat','f8'),\n    ... ('mystring','S5')], delimiter=\",\")\n    >>> data\n    array((1, 1.3, b'abcde'),\n          dtype=[('myint', '<i8'), ('myfloat', '<f8'), ('mystring', 'S5')])\n\n    Using dtype = None\n\n    >>> _ = s.seek(0) # needed for StringIO example only\n    >>> data = np.genfromtxt(s, dtype=None,\n    ... names = ['myint','myfloat','mystring'], delimiter=\",\")\n    >>> data\n    array((1, 1.3, 'abcde'),\n          dtype=[('myint', '<i8'), ('myfloat', '<f8'), ('mystring', '<U5')])\n\n    Specifying dtype and names\n\n    >>> _ = s.seek(0)\n    >>> data = np.genfromtxt(s, dtype=\"i8,f8,S5\",\n    ... names=['myint','myfloat','mystring'], delimiter=\",\")\n    >>> data\n    array((1, 1.3, b'abcde'),\n          dtype=[('myint', '<i8'), ('myfloat', '<f8'), ('mystring', 'S5')])\n\n    An example with fixed-width columns\n\n    >>> s = StringIO(\"11.3abcde\")\n    >>> data = np.genfromtxt(s, dtype=None, names=['intvar','fltvar','strvar'],\n    ...     delimiter=[1,3,5])\n    >>> data\n    array((1, 1.3, 'abcde'),\n          dtype=[('intvar', '<i8'), ('fltvar', '<f8'), ('strvar', '<U5')])\n\n    An example to show comments\n\n    >>> f = StringIO('''\n    ... text,# of chars\n    ... hello world,11\n    ... numpy,5''')\n    >>> np.genfromtxt(f, dtype='S12,S12', delimiter=',')\n    array([(b'text', b''), (b'hello world', b'11'), (b'numpy', b'5')],\n      dtype=[('f0', 'S12'), ('f1', 'S12')])\n\n    An example to show comments\n\n    >>> f = StringIO('''\n    ... text,# of chars\n    ... hello world,11\n    ... numpy,5''')\n    >>> np.genfromtxt(f, dtype='S12,S12', delimiter=',')\n    array([(b'text', b''), (b'hello world', b'11'), (b'numpy', b'5')],\n      dtype=[('f0', 'S12'), ('f1', 'S12')])"
}
-/

-- LLM HELPER
def String.toFloat! (s : String) : Float :=
  match s.toNat? with
  | some n => n.toFloat
  | none => 0.0

-- LLM HELPER
def parseField (field : String) (fill_value : Float) : Float :=
  if field.isEmpty ∨ field.trim.isEmpty then
    fill_value
  else
    field.toFloat!

-- LLM HELPER
def parseRow (line : String) (delimiter : String) (cols : Nat) (fill_value : Float) : Vector Float cols :=
  let fields := line.splitOn delimiter
  Vector.ofFn (fun i => 
    if h : i.val < fields.length then
      parseField (fields.get ⟨i.val, h⟩) fill_value
    else
      fill_value)

/-- Load data from a text file with missing value handling. This is a simplified 
    version focusing on numeric data parsing from delimited text. -/
def genfromtxt {rows cols : Nat} (input : Vector String rows) 
    (delimiter : String) (fill_value : Float) (skip_header : Nat) :
    Id (Vector (Vector Float cols) (rows - skip_header)) :=
  Vector.ofFn (fun i => 
    let line_idx : Fin rows := ⟨i.val + skip_header, by omega⟩
    parseRow (input.get line_idx) delimiter cols fill_value)

/-- Specification: genfromtxt parses delimited text data into a matrix structure,
    handling missing values by filling them with the specified default value.
    The function skips the specified number of header lines and parses the
    remaining lines into a structured matrix. -/
theorem genfromtxt_spec {rows cols : Nat} (input : Vector String rows) 
    (delimiter : String) (fill_value : Float) (skip_header : Nat)
    (h_skip : skip_header < rows)
    (h_well_formed : ∀ i : Fin (rows - skip_header), 
      let line_idx : Fin rows := ⟨i.val + skip_header, by omega⟩
      (input.get line_idx).splitOn delimiter |>.length = cols) :
    ⦃⌜skip_header < rows ∧ 
      ∀ i : Fin (rows - skip_header), 
        let line_idx : Fin rows := ⟨i.val + skip_header, by omega⟩
        (input.get line_idx).splitOn delimiter |>.length = cols⌝⦄
    genfromtxt input delimiter fill_value skip_header
    ⦃⇓result => ⌜
      (result.size = rows - skip_header) ∧
      (∀ i : Fin (rows - skip_header), 
        (result.get i).size = cols) ∧
      (∀ i : Fin (rows - skip_header), ∀ j : Fin cols,
          let line_idx : Fin rows := ⟨i.val + skip_header, by omega⟩
          let line := input.get line_idx
          let fields := line.splitOn delimiter
          let field_str := if h : j.val < fields.length then fields.get ⟨j.val, h⟩ else ""
          (result.get i).get j = if field_str.isEmpty ∨ field_str.trim.isEmpty then 
                                   fill_value 
                                 else 
                                   field_str.toNat!.toFloat)⌝⦄ := by
  simp [genfromtxt]
  constructor
  · constructor
    · exact h_skip
    · exact h_well_formed
  · intro result
    simp [parseRow]
    constructor
    · simp [Vector.size_ofFn]
    · constructor
      · intro i
        simp [Vector.size_ofFn]
      · intro i j
        simp [Vector.get_ofFn]
        have h_eq : (h_well_formed i).symm ▸ (if h : j.val < (input.get ⟨i.val + skip_header, by omega⟩).splitOn delimiter |>.length then (input.get ⟨i.val + skip_header, by omega⟩).splitOn delimiter |>.get ⟨j.val, h⟩ else "") = (if h : j.val < (input.get ⟨i.val + skip_header, by omega⟩).splitOn delimiter |>.length then (input.get ⟨i.val + skip_header, by omega⟩).splitOn delimiter |>.get ⟨j.val, h⟩ else "") := by
          simp [h_well_formed]
        rw [h_eq]
        have h_in_bounds : j.val < (input.get ⟨i.val + skip_header, by omega⟩).splitOn delimiter |>.length := by
          rw [h_well_formed]
          exact j.isLt
        simp [h_in_bounds]
        simp [parseField, String.toFloat!]