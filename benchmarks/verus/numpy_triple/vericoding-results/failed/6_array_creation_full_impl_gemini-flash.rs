// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add ExClone bound to T */
fn full<T: vstd::std_specs::clone::ExClone>(n: usize, fill_value: T) -> (result: Vec<T>)
    ensures 
        result.len() == n,

        forall|i: int| 0 <= i < n ==> result[i] == fill_value,

        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> result[i] == result[j],

        n > 0 ==> result[0] == fill_value,
        n > 0 ==> result[(n-1) as int] == fill_value,
{}
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
/* code modified by LLM (iteration 5): added the `ExClone` bound for the `T` type */
{
    let mut result: Vec<T> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            // All elements inserted so far are equal to the initial fill_value
            forall|j: int| 0 <= j < i as int ==> result[j] == fill_value.clone(),
            i <= n,
    {
        result.push(fill_value.clone());
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}