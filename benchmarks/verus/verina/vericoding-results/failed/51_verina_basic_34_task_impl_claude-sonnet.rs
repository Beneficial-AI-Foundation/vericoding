// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified helper to just check even property */
fn is_even_exec(n: i32) -> (b: bool)
    ensures b == is_even(n)
{
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
    /* code modified by LLM (iteration 5): simplified loop invariants and strengthened proof blocks */
    let mut result = Vec::new();
    let mut idx = 0;
    
    while idx < arr.len()
        invariant
            0 <= idx <= arr.len(),
            forall|x: i32| result@.contains(x) ==> is_even(x) && arr@.contains(x),
            forall|k: int| 0 <= k < idx && is_even(arr[k]) ==> result@.contains(arr[k]),
            forall|k1: int, k2: int| 0 <= k1 < k2 < idx && is_even(arr[k1]) && is_even(arr[k2]) ==> {
                exists|r1: int, r2: int| 0 <= r1 < r2 < result.len() && 
                    result[r1] == arr[k1] && result[r2] == arr[k2]
            },
        decreases arr.len() - idx
    {
        if is_even_exec(arr[idx]) {
            result.push(arr[idx]);
            
            proof {
                let old_len = result.len() - 1;
                assert(result[old_len] == arr[idx as int]);
                
                // Establish that all previous even elements maintain their relative positions
                assert(forall|k: int| 0 <= k < idx && is_even(arr[k]) ==> {
                    exists|rk: int| 0 <= rk < old_len && result[rk] == arr[k]
                });
                
                // For order preservation with the new element
                assert(forall|k: int| 0 <= k < idx && is_even(arr[k]) ==> {
                    let rk = choose|r: int| 0 <= r < old_len && result[r] == arr[k];
                    rk < old_len && old_len < result.len()
                });
            }
        }
        idx += 1;
    }
    
    proof {
        // Final proof that order is preserved for all pairs
        assert(forall|i: int, j: int| 0 <= i <= j < arr.len() && is_even(arr[i]) && is_even(arr[j]) ==> {
            if i == j {
                let ri = choose|r: int| 0 <= r < result.len() && result[r] == arr[i];
                ri <= ri
            } else {
                let ri = choose|r1: int| 0 <= r1 < result.len() && result[r1] == arr[i];
                let rj = choose|r2: int| 0 <= r2 < result.len() && result[r2] == arr[j];
                ri <= rj
            }
        });
    }
    
    result
}
// </vc-code>

}
fn main() {}