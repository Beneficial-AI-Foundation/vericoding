// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MyMin(a: int, b: int) returns (result: int)
    ensures result <= a && result <= b
    ensures result == a || result == b
// </vc-spec>
// <vc-code>
{
  if a <= b {
    result := a;
  } else {
    result := b;
  }
}
// </vc-code>
