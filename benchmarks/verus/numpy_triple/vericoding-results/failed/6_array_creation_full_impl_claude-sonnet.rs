// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 5): Removed clone() calls and used references to avoid Clone trait requirement */
    let mut result = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k] == fill_value,
        decreases n - i
    {
        result.push(fill_value);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}