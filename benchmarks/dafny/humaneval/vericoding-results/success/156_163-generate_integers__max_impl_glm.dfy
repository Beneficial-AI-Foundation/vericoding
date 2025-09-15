// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method max(a : int, b : int) returns (m : int)
  ensures m == a || m == b
  ensures m >= a && m >= b
// </vc-spec>
// <vc-code>
{
  m := if a >= b then a else b;
}
// </vc-code>
