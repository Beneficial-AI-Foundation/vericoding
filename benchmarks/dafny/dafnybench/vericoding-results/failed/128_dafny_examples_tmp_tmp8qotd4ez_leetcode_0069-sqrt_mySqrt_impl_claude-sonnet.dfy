// Author: Shaobo He

predicate sqrt(x: int, r: int) {
    r*r <= x && (r+1)*(r+1) > x
}

// <vc-helpers>
lemma SqrtExists(x: int)
    requires x >= 0
    ensures exists r: int :: r >= 0 && sqrt(x, r)
{
    var r := 0;
    while r * r <= x
        invariant r >= 0
        decreases x - r * r + 1
    {
        if (r + 1) * (r + 1) > x {
            assert sqrt(x, r);
            return;
        }
        r := r + 1;
    }
    assert r > 0;
    assert r * r > x;
    var prev := r - 1;
    assert prev >= 0;
    assert prev * prev <= x;
    assert (prev + 1) * (prev + 1) > x;
    assert sqrt(x, prev);
}

lemma SqrtUnique(x: int, r1: int, r2: int)
    requires x >= 0
    requires sqrt(x, r1)
    requires sqrt(x, r2)
    ensures r1 == r2
{
    if r1 < r2 {
        assert (r1 + 1) * (r1 + 1) > x;
        assert r2 * r2 <= x;
        assert r1 + 1 <= r2;
        assert (r1 + 1) * (r1 + 1) <= r2 * r2;
        assert false;
    } else if r1 > r2 {
        assert (r2 + 1) * (r2 + 1) > x;
        assert r1 * r1 <= x;
        assert r2 + 1 <= r1;
        assert (r2 + 1) * (r2 + 1) <= r1 * r1;
        assert false;
    }
}
// </vc-helpers>

// <vc-spec>
method mySqrt(x: int) returns (res: int)
requires 0 <= x;
ensures sqrt(x, res);
// </vc-spec>
// <vc-code>
{
    res := 0;
    while (res + 1) * (res + 1) <= x
        invariant res >= 0
        invariant res * res <= x
        decreases x - res * res
    {
        res := res + 1;
    }
    assert (res + 1) * (res + 1) > x;
    assert sqrt(x, res);
}
// </vc-code>

