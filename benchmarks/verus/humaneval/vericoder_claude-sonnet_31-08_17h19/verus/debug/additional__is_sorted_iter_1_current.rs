use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_sorted_witness(lst: &[i32], pos: usize)
    requires
        lst.len() >= 1,
        pos < lst.len() - 1,
        lst[pos as int] > lst[pos as int + 1],
    ensures
        exists|i: int, j: int| 0 <= i && i < j && j < lst.len() && lst[i] > lst[j],
{
    assert(0 <= pos && pos < pos + 1 && pos + 1 < lst.len() && lst[pos as int] > lst[pos as int + 1]);
}

proof fn lemma_not_sorted_implies_witness(lst: &[i32])
    requires
        lst.len() >= 1,
        !(forall|i: int, j: int| 0 <= i && i < j && j < lst.len() ==> lst[i] <= lst[j]),
    ensures
        exists|i: int, j: int| 0 <= i && i < j && j < lst.len() && lst[i] > lst[j],
{
    assert(exists|i: int, j: int| 0 <= i && i < j && j < lst.len() && lst[i] > lst[j]);
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
    let mut i = 0;
    while i < lst.len() - 1
        invariant
            0 <= i <= lst.len() - 1,
            forall|k: int, l: int| 0 <= k && k < l && l < i + 1 ==> lst[k] <= lst[l],
    {
        if lst[i] > lst[i + 1] {
            proof {
                lemma_sorted_witness(lst, i);
            }
            return false;
        }
        i += 1;
    }
    
    proof {
        assert(forall|k: int, l: int| 0 <= k && k < l && l < lst.len() ==> lst[k] <= lst[l]) by {
            assert(i == lst.len() - 1);
        }
    }
    
    true
}
// </vc-code>

fn main() {}
}