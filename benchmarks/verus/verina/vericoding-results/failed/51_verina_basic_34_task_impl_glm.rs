// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added proper function signature */
fn is_even_exec(n: i32) -> (result: bool)
    ensures result == is_even(n)
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
/* code modified by LLM (iteration 5): Added trigger to second invariant and removed proof block */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall |x: i32| result@.contains(x) ==> is_even(x) && arr@.contains(x),
            forall |j: int| #![trigger result@.contains(arr@[j])] 0 <= j < i && is_even(arr@[j]) ==> result@.contains(arr@[j]),
            forall |i1: int, i2: int| 
                0 <= i1 < i && 0 <= i2 < i && i1 <= i2 && is_even(arr@[i1]) && is_even(arr@[i2]) ==>
                exists |ri1: int, ri2: int| 
                    0 <= ri1 < result@.len() && 0 <= ri2 < result@.len() && 
                    ri1 <= ri2 && 
                    result@[ri1] == arr@[i1] && result@[ri2] == arr@[i2],
        decreases (arr.len() - i)
    {
        if is_even_exec(arr[i]) {
            result.push(arr[i]);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}