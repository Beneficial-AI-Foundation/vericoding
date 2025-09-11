// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_duplicates(a: &[i32]) -> (result: Vec<i32>)
    requires
        a.len() >= 1,
    ensures
        forall|i: int| #![auto] 0 <= i < result.len() ==> in_array(a@, result[i]),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}