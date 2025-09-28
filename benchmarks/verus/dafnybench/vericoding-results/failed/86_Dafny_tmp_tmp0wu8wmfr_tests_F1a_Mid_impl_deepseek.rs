use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn mid_lemma(p: int, q: int)
    requires
        p <= q,
    ensures
        exists|m: int| p <= m <= q && m - p <= q - m && 0 <= (q - m) - (m - p) <= 1
{
    let diff: int = q - p;
    let mid_point: int = p + diff / 2;
    assert(p <= mid_point <= q) by {
        assert(0 <= diff / 2 <= diff) by {
            assert(0 <= diff / 2);
            assert(diff / 2 <= diff);
        };
    };
    assert(mid_point - p <= q - mid_point) by {
        assert(mid_point - p == diff / 2);
        assert(q - mid_point == diff - (diff / 2));
        assert(diff / 2 <= diff - (diff / 2));
    };
    assert(0 <= (q - mid_point) - (mid_point - p) <= 1) by {
        let a = mid_point - p;
        let b = q - mid_point;
        assert(b - a == (q - p) % 2);
        assert(0 <= (q - p) % 2 <= 1);
    };
}
// </vc-helpers>

// <vc-spec>
fn mid(p: int, q: int) -> (m: int)
    // | ... | ??? | ... |
    //        p m   q
    requires 
        p <= q,
    ensures 
        p <= m <= q,
        m - p <= q - m,
        0 <= (q - m) - (m - p) <= 1,
// </vc-spec>
// <vc-code>
{
    proof {
        mid_lemma(p, q);
    }
    let diff: int = q - p;
    p + (diff / 2)
}
// </vc-code>

fn main() {
}

}