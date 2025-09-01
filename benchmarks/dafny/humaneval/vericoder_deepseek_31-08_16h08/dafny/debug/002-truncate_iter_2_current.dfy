

// <vc-helpers>
lemma FloorLemma(x: real)
  requires x >= 0.0
  ensures 0.0 <= x - (x as int) < 1.0
{
  // Use the property that casting real to int truncates towards zero
  var f := x as int;
  assert f <= x < f + 1.0;
  assert 0.0 <= x - f < 1.0;
}
// </vc-helpers>
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
  i := x as int;
  FloorLemma(x);
}
// </vc-code>

