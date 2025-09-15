// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_even_exists(arr: Seq<i32>, i: int) requires 0 <= i < arr.len(), is_even(arr[i]) ensures exists|j: int| 0 <= j < arr.len() && is_even(arr[j]) { }
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
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|k: int| 0 <= k < result.len() ==> is_even(result[k]),
            forall|k: int| 0 <= k < result.len() ==> exists|j: int| 0 <= j < arr.len() && result[k] == arr[j],
    {
        if is_even(arr[i]) {
            result.push(arr[i]);
            proof { lemma_even_exists(arr@, i); }
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}