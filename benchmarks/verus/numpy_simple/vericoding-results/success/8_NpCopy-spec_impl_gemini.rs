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
    let mut i: usize = 0;
    let mut new_vec = Vec::new();
    while i < arr.len()
        invariant
            new_vec.len() == i,
            i <= arr.len(),
            forall|j: int| 0 <= j < i ==> new_vec[j] as int == arr[j] as int,
        decreases arr.len() - i
    {
        let elem = arr[i];
        new_vec.push(elem);
        i = i + 1;
    }
    new_vec
}
// </vc-code>


}
fn main() {}