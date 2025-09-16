// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn zip_halves<T>(v: Seq<T>) -> (ret: Seq<(T, T)>) {
    v.take((v.len() / 2) as int).zip_with(v.skip(((v.len() + 1) / 2) as int).reverse())
}

spec fn diff(s: Seq<(i32, i32)>) -> (ret: int) {
    s.fold_left(
        0,
        |acc: int, x: (i32, i32)|
            if (x.0 != x.1) {
                acc + 1
            } else {
                acc
            },
    )
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): non-negativity of diff */
spec fn diff_nonneg(s: Seq<(i32, i32)>) -> bool { diff(s) >= 0 }
// </vc-helpers>

// <vc-spec>
fn smallest_change(v: Vec<i32>) -> (change: usize)

    requires
        v@.len() < usize::MAX,

    ensures
        change == diff(zip_halves(v@)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate over Vec and count mismatches between halves, with proof linking to spec */
    let n = v.len();
    let offset = (n + 1) / 2;
    let m = n / 2;
    let mut i: usize = 0;
    let mut cnt: usize = 0;
    while i < m
        invariant
            i <= m,
            (cnt as int) == diff(zip_halves(v@).take(i as int)),
        decreases m - i
    {
        if v[i] != v[i + offset] {
            cnt = cnt + 1;
        }
        i = i + 1;
    }
    proof {
        assert(zip_halves(v@).take(m as int) == zip_halves(v@));
        assert((cnt as int) == diff(zip_halves(v@)));
    }
    cnt
}
// </vc-code>

}
fn main() {}