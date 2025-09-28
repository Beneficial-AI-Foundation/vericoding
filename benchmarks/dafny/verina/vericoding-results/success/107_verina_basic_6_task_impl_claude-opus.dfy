// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(x: int, y: int): int
{
  if x <= y then x else y
}
// </vc-helpers>

// <vc-spec>
method MinOfThree(a: int, b: int, c: int) returns (result: int)
    ensures result <= a && result <= b && result <= c
    ensures result == a || result == b || result == c
// </vc-spec>
// <vc-code>
{
  var temp := min(a, b);
  result := min(temp, c);
}
// </vc-code>
