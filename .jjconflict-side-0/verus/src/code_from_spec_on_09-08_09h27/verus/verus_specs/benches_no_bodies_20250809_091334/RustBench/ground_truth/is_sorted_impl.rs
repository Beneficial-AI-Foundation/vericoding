use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn is_sorted(lst: &[i32]) -> (result: bool)
    requires
        lst.len() >= 1,
    ensures
        result <== forall|i: int, j: int| 0 <= i && i < j && j < lst.len() ==> lst[i] <= lst[j],
        !result ==> exists|i: int, j: int| 0 <= i && i < j && j < lst.len() && lst[i] > lst[j],
{
    for k in 1..lst.len()
        invariant
            forall|i: int, j: int| 0 <= i && i < j && j < k ==> lst[i] <= lst[j],
    {
        if lst[k - 1] > lst[k] {
            return false;
        }
    }
    true
}

fn main() {}
}