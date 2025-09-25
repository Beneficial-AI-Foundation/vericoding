// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted(a: &[int], l: int, u: int) -> bool {
    forall|i: int, j: int| 0 <= l <= i <= j <= u < a.len() ==> a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn binary_search(a: &[int], key: int) -> (index: i32)
    requires 
        a.len() > 0,
        sorted(a, 0, (a.len() - 1) as int),
    ensures 
        index >= 0 ==> index < a.len() && a[index as int] == key,
        index < 0 ==> forall|k: int| 0 <= k < a.len() ==> a[k] != key,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}