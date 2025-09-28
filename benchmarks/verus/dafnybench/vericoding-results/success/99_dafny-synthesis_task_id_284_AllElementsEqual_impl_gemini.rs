// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn all_elements_equal(a: &[i32], n: i32) -> (result: bool)
    ensures
        result ==> forall|i: int| 0 <= i < a.len() ==> a[i] == n,
        !result ==> exists|i: int| 0 <= i < a.len() && a[i] != n,
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|j: int| 0 <= j < (i as int) ==> a@[j] == n,
        decreases a.len() - i
    {
        if a[i] != n {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}