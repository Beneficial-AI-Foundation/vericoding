// Author: Shaobo He

predicate sqrt(x: int, r: int) {
    r*r <= x && (r+1)*(r+1) > x
}

// <vc-helpers>
lemma sqrtUnique(x: int, r1: int, r2: int)
    requires x >= 0
    requires sqrt(x, r1)
    requires sqrt(x, r2)
    ensures r1 == r2
{
    if r1 != r2 {
        if r1 < r2 {
            assert r1 + 1 <= r2;
            calc {
                (r1 + 1) * (r1 + 1);
                <= r2 * r2;
                <= x;
            }
            assert false;
        } else {
            assert r2 + 1 <= r1;
            calc {
                (r2 + 1) * (r2 + 1);
                <= r1 * r1;
                <= x;
            }
            assert false;
        }
    }
}

lemma sqrtMonotonic(x: int, y: int, rx: int, ry: int)
    requires 0 <= x <= y
    requires sqrt(x, rx)
    requires sqrt(y, ry)
    ensures rx <= ry
{
    if rx > ry {
        calc {
            y;
            >= (ry + 1) * (ry + 1);
            >= (rx) * (rx);
            > x;
        }
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
    var r := 0;
    while (r + 1) * (r + 1) <= x
        invariant 0 <= r
        invariant r * r <= x
    {
        r := r + 1;
    }
    return r;
}
// </vc-code>

