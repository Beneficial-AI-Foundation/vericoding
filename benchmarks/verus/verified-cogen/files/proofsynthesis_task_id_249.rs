// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn intersection(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)

    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && arr2@.contains(
                #[trigger] result[i],
            )),
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