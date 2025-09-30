// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MaxOfThree(a: int, b: int, c: int) returns (result: int)
    ensures result >= a && result >= b && result >= c
    ensures result == a || result == b || result == c
// </vc-spec>
// <vc-code>
{
  if a >= b && a >= c {
    result := a;
  } else if b >= a && b >= c {
    result := b;
  } else {
    result := c;
  }
}
// </vc-code>
