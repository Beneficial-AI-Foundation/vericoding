// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert usize index to int bounds */
proof fn lemma_usize_index_to_int(len: usize, i: usize)
    requires i < len,
    ensures 0 <= (i as int) && (i as int) < (len as int),
    decreases len
{
    assert(0 <= (i as int));
    assert((i as int) < (len as int));
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
    /* code modified by LLM (iteration 5): iterate to find maximum element with spec-level indexing */
    let mut i: usize = 1;
    let mut idx: usize = 0;
    let mut cur: usize = lst[0];

    while i < lst.len()
        invariant
            idx < i,
            i <= lst.len(),
            forall|j: int| 0 <= j < (i as int) ==> lst[j] <= cur,
            exists|j: int| 0 <= j < (i as int) && lst[j] == cur,
        decreases lst.len() - i
    {
        if lst[i] > cur {
            cur = lst[i];
            idx = i;
        }
        i += 1;
    }

    proof {
        assert(i == lst.len());
        assert(exists|j: int| 0 <= j < (i as int) && lst[j] == cur);
        assert(forall|j: int| 0 <= j < (i as int) ==> lst[j] <= cur);
    }

    cur
}
// </vc-code>

}
fn main() {}