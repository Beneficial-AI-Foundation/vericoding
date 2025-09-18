// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed proof functions that cause compilation errors with nat/int types */
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] + b[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Removed int/nat type conversions and fixed compilation errors */
{
    let len = a.len();
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j as usize] == a[j as usize] + b[j as usize],
        decreases len - i
    {
        let sum = a[i] + b[i];
        result.push(sum);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}