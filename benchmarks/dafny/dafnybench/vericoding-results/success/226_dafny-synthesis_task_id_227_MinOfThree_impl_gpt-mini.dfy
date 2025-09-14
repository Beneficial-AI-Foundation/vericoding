

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MinOfThree(a: int, b: int, c: int) returns (min: int)
    ensures min <= a && min <= b && min <= c
    ensures (min == a) || (min == b) || (min == c)
// </vc-spec>
// <vc-code>
{
  min := a;
  if b < min {
    min := b;
  }
  if c < min {
    min := c;
  }
}
// </vc-code>

