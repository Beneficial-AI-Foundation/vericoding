// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): cast nonneg proof for usize to int */
proof fn lemma_usize_to_int_nonneg(x: usize) {
    assert((x as int) >= 0);
}
// </vc-helpers>

// <vc-spec>
fn max_of_list(lst: &Vec<usize>) -> (result: usize)
    requires lst.len() > 0,
    ensures
        exists|i: int| 0 <= i < lst.len() && lst[i] == result,
        forall|i: int| 0 <= i < lst.len() ==> lst[i] <= result,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): compute maximum value and maintain invariants without proof blocks */
    let mut i: usize = 1;
    let mut max_idx: usize = 0;
    let mut max_val: usize = lst[0];

    while i < lst.len()
        invariant
            i <= lst.len(),
            max_idx < i,
            lst[max_idx as int] == max_val,
            forall|k: int| 0 <= k < i as int ==> lst[k] <= max_val,
        decreases lst.len() - i
    {
        let v = lst[i];
        let old_max = max_val;
        if v > old_max {
            max_val = v;
            max_idx = i;
        }
        // For all k < i, we already have lst[k] <= old_max
        assert(forall|k: int| 0 <= k < i as int ==> lst[k] <= old_max);
        if v > old_max {
            assert(lst[i as int] <= max_val);
        } else {
            assert(lst[i as int] <= max_val);
        }
        assert(forall|k: int| 0 <= k < (i + 1) as int ==> lst[k] <= max_val);

        i += 1;
    }

    let result = max_val;
    // max_idx is a valid index and points to the maximum value
    assert(max_idx < lst.len());
    assert(lst[max_idx as int] == result);
    // All elements are <= result by the loop invariant at termination
    assert(forall|k: int| 0 <= k < lst.len() as int ==> lst[k] <= result);
    // There exists an index with lst[index] == result
    assert(exists|j: int| 0 <= j < lst.len() as int && lst[j] == result);

    result
}
// </vc-code>

}
fn main() {}