

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method truncate(x : real) returns (i : real)
    // pre-conditions-start
    requires x >= 0.0
    // pre-conditions-end
    // post-conditions-start
    ensures (0.0 <= x - i < 1.0)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  i := 0.0;
  while x - i >= 1.0
    invariant 0.0 <= i <= x
    decreases x - i
  {
    i := i + 1.0;
  }
}
// </vc-code>

