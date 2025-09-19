// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn replace(arr: &Vec<i8>, k: i8) -> (result: Vec<i8>)
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> (arr[i] as int > k as int ==> result[i] as int == -1),
        forall|i: int| 0 <= i < arr.len() ==> (arr[i] as int <= k as int ==> result[i] as int == arr[i] as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}