// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn cube_elements(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] * a[i] * a[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): changed `i32` to `int` for intermediate calculations to prevent overflow */
{
    let mut result = Vec::new();
    result.reserve(a.len());
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (a[j] as int * a[j] as int * a[j] as int) as i32,
        decreases a.len() - i
    {
        result.push((a[i] as int * a[i] as int * a[i] as int) as i32);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}