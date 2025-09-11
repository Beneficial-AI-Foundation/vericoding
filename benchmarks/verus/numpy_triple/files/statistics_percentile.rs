// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn percentile(arr: Vec<i32>, q: i32) -> (result: i32)
    requires 
        arr.len() > 0,
        0 <= q && q <= 100,
    ensures
        (forall|i: int| 0 <= i < arr.len() ==> arr[i] <= result ==> 
            exists|j: int| 0 <= j < arr.len() && arr[j] >= result) &&
        (forall|i: int| 0 <= i < arr.len() ==> arr[i] >= result ==> 
            exists|j: int| 0 <= j < arr.len() && arr[j] <= result) &&
        (q == 0 ==> forall|i: int| 0 <= i < arr.len() ==> result <= arr[i]) &&
        (q == 100 ==> forall|i: int| 0 <= i < arr.len() ==> arr[i] <= result)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}