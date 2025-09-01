

// <vc-helpers>
lemma lemma_floor(x: real) returns (i: real)
  ensures 0.0 <= x - i < 1.0
{
    i := (x as int) as real;
    assert i <= x;
    assert x - i < 1.0;
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
    i := (x as int) as real;
    lemma_floor(x);
}
// </vc-code>

