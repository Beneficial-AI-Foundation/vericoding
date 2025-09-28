// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec helper to double integers */
spec fn times_two(x: int) -> int { 2 * x }
// </vc-helpers>

// <vc-spec>
fn double_array_elements(s: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] result[i] == 2 * s[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate and push doubled elements using i32 arithmetic and correct spec indices */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            (i as int) <= (s.len() as int),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j] == 2 * s[j],
        decreases s.len() - i
    {
        let v: i32 = s[i];
        let doubled: i32 = v * 2;
        result.push(doubled);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}