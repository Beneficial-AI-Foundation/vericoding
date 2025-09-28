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
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|x: i32| result@.contains(x) ==> is_even(x) && arr@[..i as int].contains(x),
            forall|x: i32| arr@[..i as int].contains(x) && is_even(x) ==> result@.contains(x),
            forall|j: int, k: int| 0 <= j < i && 0 <= k < i && j <= k && 
                is_even(arr[j]) && is_even(arr[k]) ==> {
                    exists|rj: int, rk: int| 0 <= rj < result.len() && 0 <= rk < result.len() && 
                        rj <= rk && result[rj] == arr[j] && result[rk] == arr[k]
                },
    {
        if is_even(arr[i]) {
            result.push(arr[i]);
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}