// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial helper kept for compatibility */
spec fn helper_true() -> bool { true }
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
    /* code modified by LLM (iteration 5): collect even numbers preserving order with invariants wrapped in braces */
    let mut result: Vec<i32> = Vec::new();
    let mut idx: int = 0;
    while idx < arr.len()
        invariant { 0 <= idx && idx <= arr.len() }
        invariant { forall|k: int| 0 <= k && k < result.len() ==> is_even(result@[k]) && arr@.contains(result@[k]) }
        invariant { forall|t: int| 0 <= t && t < idx && is_even(arr@[t]) ==> (exists|k: int| 0 <= k && k < result.len() && result@[k] == arr@[t]) }
        invariant { forall|a: int, b: int| 0 <= a && a < idx && 0 <= b && b < idx && a <= b && is_even(arr@[a]) && is_even(arr@[b]) ==> exists|ra: int, rb: int| 0 <= ra && ra < result.len() && 0 <= rb && rb < result.len() && ra <= rb && result@[ra] == arr@[a] && result@[rb] == arr@[b] }
        decreases arr.len() - idx
    {
        let v = arr[idx];
        if is_even(v) {
            result.push(v);
        }
        idx += 1;
    }
    result
}
// </vc-code>

}
fn main() {}