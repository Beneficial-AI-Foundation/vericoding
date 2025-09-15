// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): binary search returning insertion index with proofs of bounds and ordering */
spec fn bsearch(xs: &Vec<i32>, target: i32, lo: int, hi: int) -> int
    requires 0 <= lo && lo <= hi && hi <= xs.len() as int,
    requires forall |i: int, j: int| 0 <= i && i < j && j < xs.len() as int ==> xs[i] < xs[j],
    ensures lo <= result && result <= hi,
    ensures forall |i: int| 0 <= i && i < result ==> xs[i] < target,
    ensures result < xs.len() as int ==> target <= xs[result as usize],
    decreases hi - lo
{
    if lo == hi {
        lo
    } else {
        let mid: int = (lo + hi) / 2;
        if xs[mid as usize] < target {
            bsearch(xs, target, mid + 1, hi)
        } else {
            bsearch(xs, target, lo, mid)
        }
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
    /* code modified by LLM (iteration 5): call bsearch and cast int result to usize with proofs */
    let idx_int: int = bsearch(xs, target, 0, xs.len() as int);
    proof {
        assert(0 <= idx_int);
        assert(idx_int <= xs.len() as int);
        assert(forall |i: int| 0 <= i && i < idx_int ==> xs[i] < target);
        if idx_int < xs.len() as int {
            assert(target <= xs[idx_int as usize]);
        }
    }
    idx_int as usize
}
// </vc-code>

}
fn main() {}