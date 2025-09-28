// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): swap elements using usize indices and preserve multiset */
proof fn swap_positions(v: &mut Vec<i8>, i: usize, j: usize)
    requires
        i < v.len(),
        j < v.len(),
    ensures
        v@.to_multiset() == old(v)@.to_multiset(),
{
    v.swap(i, j);
    proof {
        assert(v@.to_multiset() == old(v)@.to_multiset());
    }
}
// </vc-helpers>

// <vc-spec>
fn sort_seq_pred(s: Vec<i8>, p: Vec<bool>) -> (sorted: Vec<i8>)
    requires s.len() == p.len(),
    ensures 
        sorted.len() == s.len(),
        forall|i: int, j: int| 0 <= i < j < sorted.len() && p[i as int] && p[j as int] ==> sorted[i] as int <= sorted[j] as int,
        s@.to_multiset() == sorted@.to_multiset(),
        forall|i: int| 0 <= i < s.len() && !p[i as int] ==> sorted[i] == s[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): insertion sort among elements where p is true, using sequence indexing in invariants */
    let mut result = s.clone();

    // collect indices where p is true
    let mut idxs: Vec<usize> = Vec::new();
    let mut ii: usize = 0;
    while ii < s.len()
        invariant
            ii <= s.len(),
            idxs.len() <= s.len(),
        decreases s.len() - ii
    {
        if p[ii] {
            idxs.push(ii);
        }
        ii += 1;
    }

    let m = idxs.len();

    // insertion sort among the positions in idxs using adjacent swaps
    let mut i: usize = 1;
    while i < m
        invariant
            i <= m,
            result@.to_multiset() == s@.to_multiset(),
            forall |k: int|
                0 <= k && k < result.len() as int && !p@[k] ==> result@[k] == s@[k],
        decreases m - i
    {
        let mut j: usize = i;
        while j > 0 && result[idxs[j - 1]] > result[idxs[j]]
            invariant
                j <= i,
                result@.to_multiset() == s@.to_multiset(),
                forall |k: int|
                    0 <= k && k < result.len() as int && !p@[k] ==> result@[k] == s@[k],
            decreases j
        {
            // swap adjacent selected positions
            swap_positions(&mut result, idxs[j - 1], idxs[j]);
            j -= 1;
        }
        i += 1;
    }

    result
}
// </vc-code>


}

fn main() {}