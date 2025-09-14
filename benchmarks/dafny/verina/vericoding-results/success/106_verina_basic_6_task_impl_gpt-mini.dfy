// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a <= b then a else b }
// </vc-helpers>

// <vc-spec>
method MinOfThree(a: int, b: int, c: int) returns (result: int)
    ensures result <= a && result <= b && result <= c
    ensures result == a || result == b || result == c
// </vc-spec>
// <vc-code>
{
  if a <= b {
    if a <= c {
      result := a;
    } else {
      result := c;
    }
  } else {
    if b <= c {
      result := b;
    } else {
      result := c;
    }
  }
}
// </vc-code>
