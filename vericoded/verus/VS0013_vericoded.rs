// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn copy(arr: &Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> result[i] as int == arr[i] as int,
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i as int <= arr.len() as int,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j] as int == arr[j] as int,
        decreases arr.len() as int - i as int
    {
        result.push(arr[i]);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}