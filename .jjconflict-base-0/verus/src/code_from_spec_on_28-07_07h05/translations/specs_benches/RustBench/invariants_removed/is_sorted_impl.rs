use vstd::prelude::*;

verus! {

//IMPL is_sorted
#[verifier::loop_isolation(false)]
fn is_sorted(lst: &[i32]) -> (result: bool)
    requires
        lst.len() >= 1,
    ensures
        result <== forall|i: int, j: int| 0 <= i && i < j && j < lst.len() ==> lst[i] <= lst[j],
        !result ==> exists|i: int, j: int| 0 <= i && i < j && j < lst.len() && lst[i] > lst[j],
{
    for k in 0..lst.len() - 1
        invariant
            /* code modified by LLM (iteration 3): Removed problematic trigger annotations to fix compilation error where variable appears in both arithmetic and non-arithmetic positions */
            forall|i: int| 0 <= i < k ==> lst[i] <= lst[i + 1],
    {
        if lst[k] > lst[k + 1] {
            return false;
        }
    }
    true
}

fn main() {}
}