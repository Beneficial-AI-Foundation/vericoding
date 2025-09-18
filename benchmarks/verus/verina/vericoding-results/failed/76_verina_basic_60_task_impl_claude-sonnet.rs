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
    /* code modified by LLM (iteration 5): added proof block to establish postcondition */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|k: int| 0 <= k < result.len() ==> is_even(#[trigger] result[k]),
            forall|k: int| 0 <= k < result.len() ==> exists|j: int| 0 <= j < i && #[trigger] result[k] == arr[j],
        decreases arr.len() - i
    {
        if arr[i] % 2 == 0 {
            result.push(arr[i]);
        }
        i += 1;
    }
    
    proof {
        assert(forall|k: int| 0 <= k < result.len() ==> exists|j: int| 0 <= j < arr.len() && result[k] == arr[j]);
    }
    
    result
}
// </vc-code>

}
fn main() {}