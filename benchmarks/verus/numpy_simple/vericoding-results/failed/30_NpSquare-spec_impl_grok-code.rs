// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn square(arr: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> result[i] as int == arr[i] as int * arr[i] as int,
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::with_capacity(arr.len());
    let mut i = 0;
    while i < arr.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == arr[j] as int * arr[j] as int,
        decreases arr.len() - i,
    {
        result.push(arr[i] * arr[i]);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}