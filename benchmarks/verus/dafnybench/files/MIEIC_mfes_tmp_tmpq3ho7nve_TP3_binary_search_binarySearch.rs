// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(a: &[i32]) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn binary_search(a: &[i32], x: i32) -> (index: i32)
    requires is_sorted(a)
    ensures -1 <= index < a.len() && 
            (index != -1 ==> a[index as int] == x) &&
            (index == -1 ==> !a@.contains(x))
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}