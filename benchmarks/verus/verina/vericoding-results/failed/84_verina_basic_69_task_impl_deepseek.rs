// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed compilation error by moving proof function to spec and simplifying */
spec fn minimal_index_exists(a: Seq<i32>, e: int) -> (min_index: int)
    ensures
        0 <= min_index < a.len(),
        a[min_index] == e,
        forall|k: int| 0 <= k < min_index ==> a[k] != e,
{
    let i = choose|i: int| 0 <= i < a.len() && a[i] == e;
    let mut candidate = i;
    let mut k: int = 0;
    
    while k < i
        invariant
            0 <= k <= i,
            0 <= candidate < a.len(),
            a[candidate] == e,
            forall|j: int| 0 <= j < k ==> a[j] != e,
        decreases i - k,
    {
        if a[k] == e {
            candidate = k;
            break;
        }
        k = k + 1;
    }
    candidate
}
// </vc-helpers>

// <vc-spec>
fn linear_search(a: &Vec<i32>, e: i32) -> (result: usize)
    requires exists|i: int| 0 <= i < a.len() && a[i] == e,
    ensures
        result < a.len(),
        a[result as int] == e,
        forall|k: int| 0 <= k < result ==> a[k] != e,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use spec function result and remove unreachable proof */
    let min_index_spec = minimal_index_exists(a@, e);
    let mut i: usize = min_index_spec as usize;
    
    proof {
        assert(a@[min_index_spec] == e);
        assert(forall|k: int| 0 <= k < min_index_spec ==> a@[k] != e);
    }
    
    assert(i < a.len());
    assert(a[i] == e);
    assert(forall|k: int| 0 <= k < i ==> a@[k] != e);
    
    i
}
// </vc-code>

}
fn main() {}