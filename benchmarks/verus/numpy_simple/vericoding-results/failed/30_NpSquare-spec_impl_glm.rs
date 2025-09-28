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
    let mut result = Vec::new();
    for i in 0..arr.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == arr[j] as int * arr[j] as int,
    {
        let x = arr[i] as int;
        let square = x * x;
        result.push(square as i8);
    }
    result
}
// </vc-code>


}
fn main() {}