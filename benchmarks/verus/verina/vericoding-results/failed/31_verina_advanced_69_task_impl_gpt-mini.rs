// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): transitivity of < */
proof fn lt_trans(a: int, b: int, c: int)
    requires
        a < b,
        b < c,
    ensures
        a < c,
{
    proof {
        assert(a < b);
        assert(b < c);
        assert(a < c);
    }
}

/* helper modified by LLM (iteration 5): extract ordering from sorted vector */
proof fn vec_sorted_elim(xs: &Vec<i32>, i: int, j: int)
    requires
        forall|a: int, b: int| 0 <= a < b < xs.len() as int ==> xs@[a] < xs@[b],
        0 <= i < j < xs.len() as int,
    ensures
        xs@[i] < xs@[j],
{
    proof {
        assert(xs@[i] < xs@[j]);
    }
}
// </vc-helpers>

// <vc-spec>
fn search_insert(xs: &Vec<i32>, target: i32) -> (result: usize)
    requires forall|i: int, j: int| 0 <= i < j < xs.len() ==> xs[i] < xs[j],
    ensures
        result <= xs.len(),
        forall|i: int| 0 <= i < result ==> xs[i] < target,
        result < xs.len() ==> target <= xs[result as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use runtime indexing in condition to avoid spec int usage */
    let n: usize = xs.len();
    let mut lo: usize = 0;
    let mut hi: usize = n;
    while lo < hi
        invariant
            0 <= lo as int,
            lo as int <= hi as int,
            hi as int <= n as int,
            forall|i: int| 0 <= i < lo as int ==> xs@[i] < target,
            forall|i: int| hi as int <= i < n as int ==> target <= xs@[i],
        decreases (hi as int) - (lo as int)
    {
        let mid: usize = lo + (hi - lo) / 2;
        if xs[mid] < target {
            lo = mid + 1;
            proof {
                assert(0 <= (mid as int));
                assert((mid as int) < (n as int));
                assert(xs@[(mid as int)] < target);
                assert(forall|i: int| 0 <= i < (mid as int) ==> xs@[i] < xs@[(mid as int)]);
                assert(forall|i: int| 0 <= i < (mid as int) ==> xs@[i] < target);
                assert(forall|i: int| 0 <= i < ((mid as int) + 1) ==> xs@[i] < target);
            }
        } else {
            hi = mid;
            proof {
                assert(0 <= (mid as int));
                assert((mid as int) < (n as int));
                assert(!(xs@[(mid as int)] < target));
                assert(target <= xs@[(mid as int)]);
                assert(forall|i: int| (mid as int) <= i < n as int ==> target <= xs@[i]);
            }
        }
    }
    lo
}
// </vc-code>

}
fn main() {}