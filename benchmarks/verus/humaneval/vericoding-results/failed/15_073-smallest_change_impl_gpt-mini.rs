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
/* helper modified by LLM (iteration 5): compute half length of sequence */
spec fn half_len<T>(v: Seq<T>) -> nat { v.len() / 2 }
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
    /* code modified by LLM (iteration 5): count mismatches between symmetric elements with proper invariants and proofs */
    let n = v.len();
    let mut i: usize = 0;
    let mut cnt: usize = 0;
    while i < n / 2
        invariant
            i <= n / 2,
            cnt <= n / 2,
            (cnt as int) == diff(zip_halves(v@).take(i as int)),
            (n == 0) || (i < n),
        decreases n / 2 - i
    {
        proof {
            if n != 0 {
                assert(i < n);
                assert(n - 1 - i < n);
            }
        }
        if v[i] != v[n - 1 - i] {
            cnt = cnt + 1;
        }
        i = i + 1;
    }
    cnt
}
// </vc-code>

}
fn main() {}