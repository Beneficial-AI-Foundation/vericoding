

// <vc-helpers>
lemma FloorLemma(x: real)
  requires x >= 0.0
  ensures 0.0 <= x - (x as real as int) < 1.0
{
  // Use the property that casting real to int truncates towards zero
  var f := x as int;
  assert f as real <= x < (f + 1) as real;
  assert 0.0 <= x - (f as real) < 1.0;
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
  var i_int := x as int;
  i := i_int as real;
  FloorLemma(x);
}
// </vc-code>

