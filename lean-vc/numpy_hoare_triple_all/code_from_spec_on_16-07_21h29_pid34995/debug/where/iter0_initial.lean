import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.where",
  "category": "Searching",
  "description": "Return elements chosen from x or y depending on condition",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.where.html",
  "doc": "Return elements chosen from \`x\` or \`y\` depending on \`condition\`.\n\nNote\n----\nWhen only \`condition\` is provided, this function is a shorthand for\n\`\`np.asarray(condition).nonzero()\`\`. Using \`nonzero\` directly should be\npreferred, as it behaves correctly for subclasses. The rest of this\ndocumentation covers only the case where all three arguments are\nprovided.\n\nParameters\n----------\ncondition : array_like, bool\n    Where True, yield \`x\`, otherwise yield \`y\`.\nx, y : array_like\n    Values from which to choose. \`x\`, \`y\` and \`condition\` need to be\n    broadcastable to some shape.\n\nReturns\n-------\nout : ndarray\n    An array with elements from \`x\` where \`condition\` is True, and elements\n    from \`y\` elsewhere.\n\nSee Also\n--------\nchoose\nnonzero : The function that is called when x and y are omitted",
  "code": "@array_function_dispatch(_where_dispatcher)\ndef where(condition, x=None, y=None):\n    \"\"\"\n    Return elements chosen from \`x\` or \`y\` depending on \`condition\`.\n\n    Note\n    ----\n    When only \`condition\` is provided, this function is a shorthand for\n    \`\`np.asarray(condition).nonzero()\`\`. Using \`nonzero\` directly should be\n    preferred, as it behaves correctly for subclasses. The rest of this\n    documentation covers only the case where all three arguments are\n    provided.\n\n    Parameters\n    ----------\n    condition : array_like, bool\n        Where True, yield \`x\`, otherwise yield \`y\`.\n    x, y : array_like\n        Values from which to choose. \`x\`, \`y\` and \`condition\` need to be\n        broadcastable to some shape.\n\n    Returns\n    -------\n    out : ndarray\n        An array with elements from \`x\` where \`condition\` is True, and elements\n        from \`y\` elsewhere.\n\n    See Also\n    --------\n    choose\n    nonzero : The function that is called when x and y are omitted\n\n    Notes\n    -----\n    If all the arrays are 1-D, \`where\` is equivalent to::\n\n        [xv if c else yv\n         for c, xv, yv in zip(condition, x, y)]\n\n    \"\"\"\n    if x is None and y is None:\n        return nonzero(condition)\n    elif x is None or y is None:\n        raise ValueError(\"either both or neither of x and y should be given\")\n    return _where(condition, x, y)"
}
-/

open Std.Do

-- LLM HELPER
def select_element (cond : Bool) (x y : Float) : Float :=
  if cond then x else y

/-- Return elements chosen from x or y depending on condition.
    For each position i, if condition[i] is True, take x[i], otherwise take y[i]. -/
def numpy_where {n : Nat} (condition : Vector Bool n) (x y : Vector Float n) : Id (Vector Float n) :=
  do
    let result := Vector.zipWith3 select_element condition x y
    return result

/-- Specification: numpy_where returns an array where elements are chosen from x when condition is True,
    and from y when condition is False. -/
theorem numpy_where_spec {n : Nat} (condition : Vector Bool n) (x y : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_where condition x y
    ⦃⇓result => ⌜∀ i : Fin n, 
      (condition.get i = true → result.get i = x.get i) ∧
      (condition.get i = false → result.get i = y.get i)⌝⦄ := by
  simp [numpy_where]
  simp [HoareLogic.terminates_with_result]
  intro i
  constructor
  · intro h
    simp [Vector.get_zipWith3, select_element, h]
  · intro h
    simp [Vector.get_zipWith3, select_element, h]