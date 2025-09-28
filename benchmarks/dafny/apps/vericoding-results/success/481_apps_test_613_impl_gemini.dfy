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
lemma SubcaseProof(t: int, a: int, b: int)
    requires t == 2 && a == 3 && b > 10000
    ensures (a != t && (a - b) % (t - a) == 0)
{
    // Dafny can prove that for any integer x, x % -1 == 0.
}
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
  if a == t {
    if a == b {
      if a == 1 {
        res := "inf";
      } else {
        res := "2";
      }
    } else { // a != b
      res := "0";
    }
  } else { // a != t
    if (a - b) % (t - a) == 0 {
      res := "0";
    } else {
      if t == b {
        res := "0";
      } else {
        res := "1";
      }
    }
  }
}
// </vc-code>

