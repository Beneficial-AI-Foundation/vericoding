

// <vc-helpers>
function Floor(x: real): real
{
  if x >= 0.0 then real.Floor(x) else real.Ceiling(x)
}
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
  i := Floor(x);
}
// </vc-code>

