// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function minInt(a: int, b: int): int { if a <= b then a else b }
// </vc-helpers>

// <vc-spec>
method min(a : int, b : int) returns (m : int)
  ensures m == a || m == b
  ensures m <= a && m <= b
// </vc-spec>
// <vc-code>
{
  if a <= b {
    m := a;
  } else {
    m := b;
  }
}
// </vc-code>
