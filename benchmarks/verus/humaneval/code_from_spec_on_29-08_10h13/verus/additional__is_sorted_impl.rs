use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_sorted_implies_adjacent_sorted(lst: &[i32], i: usize)
    requires
        lst.len() >= 1,
        i < lst.len() - 1,
        forall|k: int, l: int| 0 <= k && k < l && l < lst.len() ==> lst[k] <= lst[l],
    ensures
        lst[i as int] <= lst[i + 1],
{
}

proof fn lemma_adjacent_unsorted_implies_exists_unsorted_pair(lst: &[i32], i: usize)
    requires
        lst.len() >= 1,
        i < lst.len() - 1,
        lst[i as int] > lst[i + 1],
    ensures
        exists|k: int, l: int| 0 <= k && k < l && l < lst.len() && lst[k] > lst[l],
{
    assert(lst[i as int] > lst[(i + 1) as int]);
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "fn is_sorted(lst: &[i32]) -> (result: bool)"
docstring: Sort elements according to specified criteria.
*/
// </vc-description>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn is_sorted(lst: &[i32]) -> (result: bool)
    // pre-conditions-start
    requires
        lst.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result <== forall|i: int, j: int| 0 <= i && i < j && j < lst.len() ==> lst[i] <= lst[j],
        !result ==> exists|i: int, j: int| 0 <= i && i < j && j < lst.len() && lst[i] > lst[j],
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut i = 0;
    /* code modified by LLM (iteration 5): fixed loop invariant to properly establish sorted property for initial range */
    while i < lst.len() - 1
        invariant
            i <= lst.len() - 1,
            forall|k: int, l: int| 0 <= k && k < l && l <= i ==> lst[k] <= lst[l],
        decreases lst.len() - 1 - i
    {
        if lst[i] > lst[i + 1] {
            proof {
                lemma_adjacent_unsorted_implies_exists_unsorted_pair(lst, i);
            }
            return false;
        }
        i = i + 1;
    }
    
    proof {
        assert(forall|k: int, l: int| 0 <= k && k < l && l < lst.len() ==> lst[k] <= lst[l]) by {
            assert(forall|k: int, l: int| 0 <= k && k < l && l <= lst.len() - 1 ==> lst[k] <= lst[l]);
        }
    }
    
    true
}
// </vc-code>

fn main() {}
}