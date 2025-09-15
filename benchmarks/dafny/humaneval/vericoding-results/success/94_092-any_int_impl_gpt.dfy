// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate OneIsSum(a: int, b: int, c: int)
{
  a == b + c || b == a + c || c == a + b
}
// </vc-helpers>

// <vc-spec>
method any_int(a: int, b: int, c: int) returns (r: bool)

  ensures r == (a == b + c || b == a + c || c == a + b)
// </vc-spec>
// <vc-code>
{
  r := OneIsSum(a, b, c);
}
// </vc-code>
