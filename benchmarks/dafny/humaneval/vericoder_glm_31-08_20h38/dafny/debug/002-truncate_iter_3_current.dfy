

// <vc-helpers>
import opened Math

lemma truncate_lemma(x: real)
    requires 0.0 <= x
    ensures exists i :: 0.0 <= x - i < 1.0 && i == floor(x)
{
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

