predicate ValidInput(a: int, b: int, x: int)
{
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= x <= 200
}

predicate CanHaveExactlyCats(a: int, b: int, x: int)
{
    a <= x <= a + b
}

// <vc-helpers>
lemma ExactlyCatsLemma(a: int, b: int, x: int)
  requires ValidInput(a, b, x)
  ensures CanHaveExactlyCats(a, b, x) <==> (x <= a + b && x >= a)
{
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, x: int) returns (result: string)
    requires ValidInput(a, b, x)
    ensures result == "YES" <==> CanHaveExactlyCats(a, b, x)
// </vc-spec>
// <vc-code>
{
  if x <= a + b && x >= a {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>

