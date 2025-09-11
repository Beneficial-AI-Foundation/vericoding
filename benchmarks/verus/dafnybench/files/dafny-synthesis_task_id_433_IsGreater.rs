// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_greater(n: i32, a: &[i32]) -> (result: bool)
    ensures 
        result ==> forall|i: int| 0 <= i < a.len() ==> n > a[i],
        !result ==> exists|i: int| 0 <= i < a.len() && n <= a[i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}