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
/* code modified by LLM (iteration 5): Fixed type errors by using `usize` for array indexing and loop bounds, and `int` for ghost code. */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i as int <= arr.len() as int,
            forall|k: int| 0 <= k < result.len() as int ==> is_even(result@[(k as usize)]),
            forall|k: int| 0 <= k < result.len() as int ==> arr@.contains(result@[(k as usize)]),
            forall|x: i32| (exists|k: int| 0 <= k < i as int && is_even(arr@[k]) && arr@[k] == x) ==> result@.contains(x),
            forall|x: i32| result@.contains(x) ==> (exists|k: int| 0 <= k < i as int && is_even(arr@[k]) && arr@[k] == x),
    {
        let val = arr@[i as int];
        if is_even(val) {
            result.push(val);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}