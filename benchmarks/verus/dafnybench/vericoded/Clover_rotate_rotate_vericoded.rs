// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn rotate(a: &[i32], offset: usize) -> (result: Vec<i32>)
    requires 
        offset >= 0,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[(i + offset as int) % a.len() as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): use u128 for intermediate calculations to prevent overflow */
    let n = a.len();
    let mut result = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            n == a.len(),
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> 
                result@[j] == a@[(j + offset as int) % (n as int)],
        decreases n - i
    {
        // The addition `i + offset` could overflow usize.
        // To avoid this, we perform the calculation using u128, which is wide enough.
        // The result of the modulo will be less than n, so it will fit back into usize.
        let source_idx = ((i as u128 + offset as u128) % (n as u128)) as usize;
        result.push(a[source_idx]);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}