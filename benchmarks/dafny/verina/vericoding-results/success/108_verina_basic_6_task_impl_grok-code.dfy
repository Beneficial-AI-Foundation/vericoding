// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int
  ensures min(a, b) <= a && min(a, b) <= b
  ensures min(a, b) == a || min(a, b) == b
{
  if a <= b then a else b
}
// </vc-helpers>

// <vc-spec>
method MinOfThree(a: int, b: int, c: int) returns (result: int)
    ensures result <= a && result <= b && result <= c
    ensures result == a || result == b || result == c
// </vc-spec>
// <vc-code>
{
  var m1 := min(a, b);
  result := min(m1, c);
}
// </vc-code>
