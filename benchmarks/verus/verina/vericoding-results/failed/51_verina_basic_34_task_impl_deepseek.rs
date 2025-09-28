// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed sequence syntax and index_of issues */
proof fn filter_even_proof(arr: Seq<i32>, i: int, result: Seq<i32>)
    requires
        0 <= i <= arr.len(),
        forall|x: i32| result.contains(x) ==> is_even(x) && arr.contains(x),
        forall|x: i32| arr.contains(x) && is_even(x) && arr.index(x) < i ==> result.contains(x),
        forall|k: int, l: int| 0 <= k < i && 0 <= l < i && k <= l && is_even(arr[k]) && is_even(arr[l]) ==> {
            exists|ri: int, rj: int| 0 <= ri < result.len() && 0 <= rj < result.len() && ri <= rj && result[ri] == arr[k] && result[rj] == arr[l]
        }
    ensures
        forall|x: i32| result.contains(x) ==> is_even(x) && arr.contains(x),
        forall|x: i32| arr.contains(x) && is_even(x) ==> result.contains(x),
        forall|k: int, l: int| 0 <= k < arr.len() && 0 <= l < arr.len() && k <= l && is_even(arr[k]) && is_even(arr[l]) ==> {
            exists|ri: int, rj: int| 0 <= ri < result.len() && 0 <= rj < result.len() && ri <= rj && result[ri] == arr[k] && result[rj] == arr[l]
        }
    decreases arr.len() - i
{
    if i < arr.len() {
        let x = arr[i];
        let new_result = if is_even(x) { result + Seq::new(1, |_: int| x) } else { result };
        filter_even_proof(arr, i + 1, new_result);
    }
}

fn is_even_exec(n: i32) -> bool {
    n % 2 == 0
}
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
    /* code modified by LLM (iteration 5): Fixed while loop with proper sequence syntax */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|x: i32| result@.contains(x) ==> is_even(x) && arr@.contains(x),
            forall|x: i32| arr@.contains(x) && is_even(x) && arr.index(x) < i ==> result@.contains(x),
            forall|k: int, l: int| 0 <= k < i && 0 <= l < i && k <= l && is_even(arr[k]) && is_even(arr[l]) ==> {
                exists|ri: int, rj: int| 0 <= ri < result.len() && 0 <= rj < result.len() && ri <= rj && result[ri] == arr[k] && result[rj] == arr[l]
            }
        decreases arr.len() - i
    {
        if is_even_exec(arr[i]) {
            result.push(arr[i]);
        }
        i += 1;
    }
    
    proof {
        filter_even_proof(arr@, 0, result@);
    }
    
    result
}
// </vc-code>

}
fn main() {}