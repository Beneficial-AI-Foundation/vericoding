predicate ValidInput(t: int, a: int, b: int)
{
    t > 0 && a > 0 && b > 0
}

predicate ValidOutput(res: string)
{
    res == "0" || res == "1" || res == "2" || res == "inf"
}

predicate InfiniteCase(t: int, a: int, b: int)
{
    a == t && a == b && a == 1
}

predicate TwoSolutionsCase(t: int, a: int, b: int)
{
    a == t && a == b && a != 1
}

predicate ZeroSolutionsCase(t: int, a: int, b: int)
{
    (t == 2 && a == 3 && b > 10000) ||
    (a == t && a != b) ||
    (a != t && (a - b) % (t - a) == 0) ||
    (a != t && (a - b) % (t - a) != 0 && t == b)
}

predicate OneSolutionCase(t: int, a: int, b: int)
{
    a != t && (a - b) % (t - a) != 0 && t != b
}

// <vc-helpers>
// No helpers required for this implementation.
// </vc-helpers>

// <vc-spec>
method solve(t: int, a: int, b: int) returns (res: string)
    requires ValidInput(t, a, b)
    requires t != a || a == t
    ensures ValidOutput(res)
    ensures InfiniteCase(t, a, b) ==> res == "inf"
    ensures TwoSolutionsCase(t, a, b) ==> res == "2"
    ensures ZeroSolutionsCase(t, a, b) ==> res == "0"
    ensures OneSolutionCase(t, a, b) ==> res == "1"
// </vc-spec>
// <vc-code>
{
  if (a == t && a == b && a == 1) {
    res := "inf";
    return;
  }
  if (a == t && a == b && a != 1) {
    res := "2";
    return;
  }
  if (t == 2 && a == 3 && b > 10000) {
    res := "0";
    return;
  }
  if (a == t && a != b) {
    res := "0";
    return;
  }
  if (a != t) {
    var rem := (a - b) % (t - a);
    if (rem == 0) {
      res := "0";
      return;
    }
    if (t == b) {
      res := "0";
      return;
    }
    res := "1";
    return;
  }
  // Fallback (shouldn't be reachable given the predicates), ensure a valid output.
  res := "0";
}
// </vc-code>

