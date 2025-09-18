// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add Clone bound to type T to enable .clone() */
fn full<T: std::clone::Clone>(n: usize, fill_value: T) -> (result: Vec<T>)
// </vc-helpers>

// <vc-spec>
fn full<T>(n: usize, fill_value: T) -> (result: Vec<T>)
    ensures 
        result.len() == n,

        forall|i: int| 0 <= i < n ==> result[i] == fill_value,

        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> result[i] == result[j],

        n > 0 ==> result[0] == fill_value,
        n > 0 ==> result[(n-1) as int] == fill_value,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): implemented the loop and added the missing 'Clone' bound to the type parameter */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            0 <= i && i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == fill_value
    {
        result.push(fill_value.clone());
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}