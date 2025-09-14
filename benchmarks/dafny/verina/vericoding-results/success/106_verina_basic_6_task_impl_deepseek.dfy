// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function minOfTwo(a: int, b: int): int {
  if a < b then a else b
}
// </vc-helpers>

// <vc-spec>
method MinOfThree(a: int, b: int, c: int) returns (result: int)
    ensures result <= a && result <= b && result <= c
    ensures result == a || result == b || result == c
// </vc-spec>
// <vc-code>
{
  var temp1 := minOfTwo(a, b);
  result := minOfTwo(temp1, c);
  assert result <= a && result <= b && result <= c;
  assert result == a || result == b || result == c;
}
// </vc-code>
