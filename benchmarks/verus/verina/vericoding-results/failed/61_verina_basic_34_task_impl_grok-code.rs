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
/* code modified by LLM (iteration 5): used spec fn is_even in exec code, fixed invariants for ordering */{
    let mut result = Vec::new();
    let ghost_arr = Ghost(arr@);
    let mut j = 0;
    while j < arr.len()
        invariant
            0 <= j <= arr.len(),
            forall|k: int| 0 <= k < j && is_even(ghost_arr@[k]) ==> exists|m: int| 0 <= m < result.len() && result@[m] == ghost_arr@[k],
            forall|k: int| 0 <= k < j && !is_even(ghost_arr@[k]) ==> !result@.contains(ghost_arr@[k]),
            forall|p: int, q: int| 0 <= p < q < result.len() ==> 
                exists|ip: int, iq: int| 0 <= ip < iq < j && result@[p] == ghost_arr@[ip] && result@[q] == ghost_arr@[iq] && is_even(ghost_arr@[ip]) && is_even(ghost_arr@[iq])
    {
        if is_even(arr[j]) {
            result.push(arr[j]);
        }
        j = j + 1;
    }
    result
}
// </vc-code>

}
fn main() {}