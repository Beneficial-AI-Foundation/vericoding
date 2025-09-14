// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Min(x: int, y: int): int
  ensures Min(x, y) <= x && Min(x, y) <= y
  ensures Min(x, y) == x || Min(x, y) == y
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
  var temp := Min(a, b);
  result := Min(temp, c);
}
// </vc-code>
