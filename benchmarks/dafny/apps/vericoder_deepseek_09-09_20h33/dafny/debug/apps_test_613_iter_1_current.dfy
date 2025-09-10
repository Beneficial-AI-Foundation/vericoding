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
lemma modZeroImpliesDivisible(x: int, y: int)
  requires y != 0
  ensures (x % y == 0) <==> (x % y == 0)
{
}

lemma positiveModProperty(x: int, y: int)
  requires y != 0
  ensures x % y >= 0
{
}

predicate ValidZeroCase(t: int, a: int, b: int)
{
    (t == 2 && a == 3 && b > 10000) ||
    (a == t && a != b) ||
    (t != a && (a - b) % (t - a) == 0 && t != b) ||
    (a != t && (a - b) % (t - a) != 0 && t == b)
}

lemma ValidateZeroCase(t: int, a: int, b: int)
  requires ValidInput(t, a, b)
  ensures ZeroSolutionsCase(t, a, b) <==> ValidZeroCase(t, a, b)
{
}

predicate ValidOneCase(t: int, a: int, b: int)
{
    a != t && (a - b) % (t - a) != 0 && t != b
}

lemma ValidateOneCase(t: int, a: int, b: int)
  requires ValidInput(t, a, b)
  ensures OneSolutionCase(t, a, b) <==> ValidOneCase(t, a, b)
{
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
  if a == t && b == a {
    if a == 1 {
      res := "inf";
    } else {
      res := "2";
    }
  } else if a == t && b != a {
    res := "0";
  } else {
    var diff := t - a;
    var rem := (a - b) % diff;
    if rem == 0 {
      if t == b {
        res := "0";
      } else {
        res := "0";
      }
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

