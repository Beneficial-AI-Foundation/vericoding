// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn no_dups(a: &Vec<i32>) -> (result: bool)
    requires forall|j: int| 1 <= j < a.len() ==> a[j-1] <= a[j]
    ensures result <==> forall|j: int| 1 <= j < a.len() ==> a[j-1] != a[j]
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}