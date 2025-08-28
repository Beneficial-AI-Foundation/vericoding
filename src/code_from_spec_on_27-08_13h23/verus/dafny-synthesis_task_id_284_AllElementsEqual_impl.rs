use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn all_elements_equal(a: &[i32], n: i32) -> (result: bool)
    ensures
        result ==> forall|i: int| 0 <= i < a.len() ==> a[i] == n,
        !result ==> exists|i: int| 0 <= i < a.len() && a[i] != n,
// </vc-spec>
// </vc-spec>

// <vc-code>
fn all_elements_equal(a: &[i32], n: i32) -> (result: bool)
    ensures
        result ==> forall|i: int| 0 <= i < a.len() ==> a[i] == n,
        !result ==> exists|i: int| 0 <= i < a.len() && a[i] != n,
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> a[k] == n,
    {
        if a[i] != n {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

fn main() {
}

}