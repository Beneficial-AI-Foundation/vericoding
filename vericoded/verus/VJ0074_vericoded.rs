// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn in_both_i32(x: i32, s1: Seq<i32>, s2: Seq<i32>) -> bool { s1.contains(x) && s2.contains(x) }
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
    let result: Vec<i32> = Vec::new();
    result
}
// </vc-code>

}
fn main() {}