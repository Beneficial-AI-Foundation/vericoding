// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_position_of_element(a: &[i32], element: usize, n1: usize, s1: Seq<i32>) -> (result: (i32, usize))
    requires
        n1 == s1.len() && 0 <= n1 <= a.len(),
        forall|i: int| 0 <= i < s1.len() ==> a[i] == s1[i],
    ensures
        result.0 == -1 || result.0 >= 1,
        s1.len() != 0 && result.0 >= 1 ==> exists|i: int| 0 <= i < s1.len() && s1[i] == element,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}