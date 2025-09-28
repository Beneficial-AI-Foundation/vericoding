// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn double_array_elements(s: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] result[i] == 2 * s[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed Vec indexing in executable code */
{
    let n = s.len();
    let mut result = Vec::new();
    let mut i = 0;

    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == 2 * s@[j],
        decreases n - i
    {
        proof {
            assert(i < n);
        }
        result.push(2 * s[i]);
        i += 1;
    }

    result
}
// </vc-code>

}
fn main() {}