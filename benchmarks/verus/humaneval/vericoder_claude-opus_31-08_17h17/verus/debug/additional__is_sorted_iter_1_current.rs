use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma to prove that if all consecutive elements are sorted, the entire array is sorted
proof fn sorted_consecutive_implies_sorted(lst: &[i32])
    requires
        lst.len() >= 1,
        forall|k: int| 0 <= k && k < lst.len() - 1 ==> lst[k] <= lst[k + 1],
    ensures
        forall|i: int, j: int| 0 <= i && i < j && j < lst.len() ==> lst[i] <= lst[j],
{
    assert forall|i: int, j: int| 0 <= i && i < j && j < lst.len() implies lst[i] <= lst[j] by {
        let mut k = i;
        while k < j
            invariant
                i <= k <= j,
                lst[i] <= lst[k],
        {
            if k == i {
                assert(lst[i] <= lst[i]);
            } else {
                assert(lst[k] <= lst[k + 1]);
            }
            k = k + 1;
        }
    }
}

// Helper lemma to prove that if there's an unsorted consecutive pair, the array is not sorted
proof fn unsorted_consecutive_implies_unsorted(lst: &[i32], idx: usize)
    requires
        lst.len() >= 1,
        0 <= idx < lst.len() - 1,
        lst[idx as int] > lst[idx as int + 1],
    ensures
        exists|i: int, j: int| 0 <= i && i < j && j < lst.len() && lst[i] > lst[j],
{
    assert(0 <= idx as int && idx as int < idx as int + 1 && idx as int + 1 < lst.len());
    assert(lst[idx as int] > lst[idx as int + 1]);
}
// </vc-helpers>

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
    if lst.len() == 1 {
        return true;
    }
    
    let mut i: usize = 0;
    while i < lst.len() - 1
        invariant
            0 <= i <= lst.len() - 1,
            lst.len() >= 2,
            forall|k: int| 0 <= k && k < i ==> lst[k] <= lst[k + 1],
    {
        if lst[i as int] > lst[i as int + 1] {
            proof {
                unsorted_consecutive_implies_unsorted(lst, i);
            }
            return false;
        }
        i = i + 1;
    }
    
    proof {
        sorted_consecutive_implies_sorted(lst);
    }
    true
}
// </vc-code>

fn main() {}
}