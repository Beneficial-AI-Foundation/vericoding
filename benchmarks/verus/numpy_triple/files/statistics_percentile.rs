// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn percentile(arr: Vec<i8>, q: i8) -> (result: i8)
    requires 
        arr.len() > 0,
        0 <= q && q <= 100,
    ensures
        (forall|i: int| 0 <= i < arr.len() ==> arr[i] as int <= result as int ==> 
            exists|j: int| 0 <= j < arr.len() && arr[j] as int >= result as int) &&
        (forall|i: int| 0 <= i < arr.len() ==> arr[i] as int >= result as int ==> 
            exists|j: int| 0 <= j < arr.len() && arr[j] as int <= result as int) &&
        (q == 0 ==> forall|i: int| 0 <= i < arr.len() ==> result as int <= arr[i] as int) &&
        (q == 100 ==> forall|i: int| 0 <= i < arr.len() ==> arr[i] as int <= result as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}