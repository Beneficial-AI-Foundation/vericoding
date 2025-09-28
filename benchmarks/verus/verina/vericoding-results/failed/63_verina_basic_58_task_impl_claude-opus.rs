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
{
    /* code modified by LLM (iteration 5): Fixed type error in assertion */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == 2 * s[j],
        decreases s.len() - i
    {
        let doubled = s[i];
        proof {
            assert(doubled as int * 2 == 2 * s[i as int] as int);
        }
        result.push(doubled + doubled);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}