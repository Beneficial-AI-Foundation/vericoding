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
        forall|x: i32| result@.contains(x) ==> is_even(x) && arr@.contains(x),
        forall|x: i32| arr@.contains(x) && is_even(x) ==> result@.contains(x),
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() && i <= j && 
            is_even(arr[i]) && is_even(arr[j]) ==> {
                exists|ri: int, rj: int| 0 <= ri < result.len() && 0 <= rj < result.len() && 
                    ri <= rj && result[ri] == arr[i] && result[rj] == arr[j]
            },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed invalid #[trigger] attributes from forall quantifiers in loop invariants to fix compilation errors */
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result@.len() <= arr@.len(),
            forall|k: int| 0 <= k < result@.len() ==> result@[k] % 2 == 0,
            forall|k: int| 0 <= k < result@.len() ==> exists|j: int| 0 <= j < i && arr@[j] % 2 == 0 && result@[k] == arr@[j],
            forall|j: int| 0 <= j < i && arr@[j] % 2 == 0 ==> exists|k: int| 0 <= k < result@.len() && result@[k] == arr@[j],
            forall|p: int, q: int| 0 <= p < q < result@.len() ==> {
                exists|k1: int, k2: int| 0 <= k1 < k2 < i && arr@[k1] % 2 == 0 && arr@[k2] % 2 == 0 && result@[p] == arr@[k1] && result@[q] == arr@[k2]
            }
        decreases arr.len() - i
    {
        if arr[i] % 2 == 0 {
            result.push(arr[i]);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}