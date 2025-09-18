// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn identity_vec_i32(a: Vec<i32>) -> Vec<i32> { a.clone() }
// </vc-helpers>

// <vc-spec>
fn around(a: Vec<i32>, decimals: i32) -> (result: Vec<i32>)
    requires decimals == 0,
    ensures
        result.len() == a.len(),

        forall|i: int| 0 <= i < a.len() && a[i] == 0 ==> result[i] == 0,

        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] <= a[j] ==> result[i] <= result[j],

        forall|i: int| 0 <= i < a.len() ==>
            result[i] - 1 <= a[i] && a[i] <= result[i] + 1,

        forall|i: int| 0 <= i < a.len() && a[i] >= 0 ==> result[i] >= 0,
// </vc-spec>
// <vc-code>
{
    let res = a.clone();
    res
}
// </vc-code>

}
fn main() {}