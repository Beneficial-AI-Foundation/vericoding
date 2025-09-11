// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn binary_search(a: &[i32], key: i32) -> (n: usize)
    requires 
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
    ensures 
        0 <= n <= a.len(),
        forall|i: int| 0 <= i < n ==> a[i] < key,
        n == a.len() ==> forall|i: int| 0 <= i < a.len() ==> a[i] < key,
        forall|i: int| n <= i < a.len() ==> a[i] >= key
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}