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
  result := a;
  if b > result {
    result := b;
  }
  if c > result {
    result := c;
  }
}
// </vc-code>
