// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn has_only_one_distinct_element(a: &Vec<i32>) -> (result: bool)
    requires a.len() > 0,
    ensures
        result ==> (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j]),
        !result ==> (exists|i: int| 0 <= i < a.len() && #[trigger] a[i] != a[0]),
// </vc-spec>
// <vc-code>
{
    let first = a[0];
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] == first,
        decreases a.len() - i,
    {
        if a[i] != first {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}