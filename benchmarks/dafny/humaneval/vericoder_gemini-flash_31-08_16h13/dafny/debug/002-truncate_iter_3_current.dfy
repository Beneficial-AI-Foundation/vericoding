

// <vc-helpers>
lemma lemma_floor(x: real) returns (i: real)
  ensures 0.0 <= x - i < 1.0
{
    i := real(x as int);
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
    i := real(x as int);
    lemma_floor(x);
}
// </vc-code>

