

// <vc-helpers>
lemma FloorLemma(x: real)
  requires x >= 0.0
  ensures 0.0 <= x - floor(x) < 1.0
{
  // Properties of floor: floor(x) <= x < floor(x) + 1
  var f := floor(x);
  assert f <= x < f + 1.0;
  assert 0.0 <= x - f < 1.0;
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
  i := floor(x);
  FloorLemma(x);
}
// </vc-code>

