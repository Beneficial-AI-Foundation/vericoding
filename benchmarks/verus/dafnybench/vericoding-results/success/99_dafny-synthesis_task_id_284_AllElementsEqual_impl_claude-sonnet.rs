use vstd::prelude::*;

verus! {

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
    for i in 0..a.len()
        invariant
            forall|j: int| 0 <= j < i ==> a[j] == n,
    {
        if a[i] != n {
            assert(a[i as int] != n);
            return false;
        }
    }
    true
}
// </vc-code>

fn main() {
}

}