// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn has_only_one_distinct_element(a: &[i32]) -> (result: bool)
    ensures
        result ==> forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j],
        !result ==> exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] != a[j],
// </vc-spec>
// <vc-code>
{
    if a.len() <= 1 {
        return true;
    }

    let first_val = a[0];
    let mut i: usize = 1;
    while i < a.len()
        invariant
            a.len() > 1,
            1 <= i <= a.len(),
            forall|j: int| 0 <= j < (i as int) ==> a@[j] == first_val,
        decreases a.len() - i
    {
        if a[i] != first_val {
            return false;
        }
        i = i + 1;
    }

    true
}
// </vc-code>

}
fn main() {}