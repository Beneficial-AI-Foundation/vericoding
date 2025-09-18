// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int| 0 <= i < result.len() ==> is_even(#[trigger] result[i]),
        forall|i: int| 0 <= i < result.len() ==> exists|j: int| 0 <= j < arr.len() && #[trigger] result[i] == arr[j],
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|k: int| 0 <= k < result.len() ==> is_even(#[trigger] result[k]),
            forall|k: int| 0 <= k < result.len() ==> exists|j: int| 0 <= j < i && #[trigger] result[k] == arr[j],
    {
        let elem = arr[i];
        if elem % 2 == 0 {
            result.push(elem);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}