// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn remove_element(lst: &Vec<nat>, target: nat) -> (result: Vec<nat>)
    ensures
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] != target,
        forall|i: int| 0 <= i < result.len() ==> 
            exists|j: int| 0 <= j < lst.len() && #[trigger] lst[j] == #[trigger] result[i] && lst[j] != target,
        forall|i: int, j: int| 0 <= i < j < lst.len() && lst[i] != target && lst[j] != target ==> 
            exists|k1: int, k2: int| 0 <= k1 < k2 < result.len() && 
            result[k1] == lst[i] && result[k2] == lst[j],
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<nat> = Vec::new();
    let mut i: usize = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            result.view() == lst.view().subrange(0, i as int).filter(|x: &nat| *x != target),
        decreases lst.len() - i
    {
        if lst[i] != target {
            result.push(lst[i]);
        }
        i = i + 1;
    }
    
    proof {
        let spec_seq = lst.view().filter(|x: &nat| *x != target);
        assert(result.view() == spec_seq);
        vstd::seq_lib::lemma_filter_preserves_relative_order(lst.view(), |x| *x != target);
    }

    result
}
// </vc-code>

}
fn main() {}