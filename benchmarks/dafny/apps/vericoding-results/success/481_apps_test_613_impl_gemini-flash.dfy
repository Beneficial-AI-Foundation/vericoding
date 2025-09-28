// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added precondition y != 0 and fixed a missing return */
function mod(x: int, y: int): int
  requires y != 0
{
  var r := x % y;
  if r < 0 then r + y else r
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
/* code modified by LLM (iteration 2): corrected logic for OneSolutionCase and TwoSolutionsCase, also added a case for OneSolutionCase */
{
  if InfiniteCase(t, a, b) {
    res := "inf";
  } else if TwoSolutionsCase(t, a, b) {
    res := "2";
  } else if OneSolutionCase(t, a, b) {
    res := "1";
  } else if ZeroSolutionsCase(t, a, b) {
    res := "0";
  } else {
    // This branch should not be reachable if predicates are comprehensive
    // For safety, assign a default or indicate an unexpected state
    res := "0"; // This should ideally not be reached if state space is fully covered.
  }
}
// </vc-code>
