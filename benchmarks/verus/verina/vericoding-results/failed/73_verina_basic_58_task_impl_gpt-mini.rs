// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple doubling function */
fn double(x: i32) -> (result: i32)
    ensures
        result == 2 * x,
{
    2 * x
}

// </vc-helpers>

// <vc-spec>
fn double_array_elements(s: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] result[i] == 2 * s[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build result using usize loop and helper */
    let mut result: Vec<i32> = Vec::new();
    let n: usize = s.len();
    let mut i: usize = 0usize;

    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: usize| j < i ==> #[trigger] result[j] == 2 * s[j],
        decreases n - i
    {
        let x: i32 = s[i];
        result.push(double(x));
        i = i + 1;
    }

    result
}

// </vc-code>

}
fn main() {}