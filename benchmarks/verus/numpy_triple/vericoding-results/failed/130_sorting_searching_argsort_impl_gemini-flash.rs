// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helper function needed */
// </vc-helpers>

// <vc-spec>
fn argsort(a: Vec<i32>) -> (result: Vec<usize>)
    ensures 
        result.len() == a.len(),

        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] < a.len(),

        forall|i: int, j: int| 0 <= i < j < result.len() ==> 
            a[#[trigger] result[i] as int] <= a[#[trigger] result[j] as int],

        forall|i: int, j: int| 0 <= i < j < result.len() && 
            a[#[trigger] result[i] as int] == a[#[trigger] result[j] as int] ==> 
            result[i] < result[j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Added decreases clause to the inner while loop to satisfy the Verus verifier. */
{
    let len = a.len();
    let mut result: Vec<usize> = Vec::new();
    if len == 0 {
        return result;
    }

    // Create a vector of indices from 0 to a.len() - 1
    for i in 0..len {
        result.push(i);
    }

    // Manual sorting (e.g., insertion sort) to avoid complex closure issues
    // This is a placeholder and needs a full verification for sorting
    for i in 1..len {
        let mut j = i;
        while j > 0 && (
            a[result[j-1]] > a[result[j]] || 
            (a[result[j-1]] == a[result[j]] && result[j-1] > result[j])
        )
        decreases j
        {
            let temp = result[j];
            result.set(j, result[j-1]);
            result.set(j-1, temp);
            j = j - 1;
        }
    }
    result
}
// </vc-code>

}
fn main() {}