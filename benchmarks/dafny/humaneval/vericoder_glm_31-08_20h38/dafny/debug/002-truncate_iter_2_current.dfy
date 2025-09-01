

// <vc-helpers>
lemma truncate_lemma(x: real)
    requires 0.0 <= x
    ensures exists i :: 0.0 <= x - i < 1.0 && i == floor(x)
{
    // The property is satisfied by the floor of x.
    // By definition of the floor function for non-negative x:
    // floor(x) is the greatest integer not greater than x.
    // Therefore, 0 <= x - floor(x) < 1.
    assert 0.0 <= x - floor(x) < 1.0;
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
    truncate_lemma(x);
}
// </vc-code>

