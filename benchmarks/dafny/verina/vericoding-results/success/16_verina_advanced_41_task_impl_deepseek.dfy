// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

function max(a: int, b: int): int {
  if a > b then a else b
}

// </vc-helpers>

// <vc-spec>
method MaxOfThree(a: int, b: int, c: int) returns (result: int)
    ensures result >= a && result >= b && result >= c
    ensures result == a || result == b || result == c
// </vc-spec>
// <vc-code>
{
  result := max(max(a, b), c);
}
// </vc-code>
