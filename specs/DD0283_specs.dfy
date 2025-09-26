// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method nonZeroReturn(x: int) returns (y: int)
  ensures y != 0
// </vc-spec>
// <vc-code>
{
  if x == 0 {
    return x + 1;
  } else {
    return -x;
  }
}
// </vc-code>
