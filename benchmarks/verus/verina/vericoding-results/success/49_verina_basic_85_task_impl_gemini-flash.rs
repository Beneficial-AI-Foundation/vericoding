// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn reverse(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[a.len() - 1 - i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed loop index `i` to `usize` for correct indexing and fixed type error. */
{
    let mut result: Vec<i32> = Vec::new();
    let capacity = a.len();
    result.reserve(capacity as usize);

    let mut i: usize = a.len();
    
    while i > 0
        invariant
            0 <= i <= a.len(),
            result.len() == (a.len() - i),
            forall|j: int| 0 <= j < result.len() ==> result[j] == a[a.len() - 1 - j as int]
        decreases i
    {
        i = i - 1;
        result.push(a[i as usize]);
    }

    result
}
// </vc-code>

}
fn main() {}