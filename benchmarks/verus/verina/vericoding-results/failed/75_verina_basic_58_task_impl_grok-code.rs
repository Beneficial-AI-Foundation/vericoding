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
    /* code modified by LLM (iteration 2): fixed type consistency in invariant by casting to int, fixed possible arithmetic overflow by using i64 for multiplication and casting back to i32, adjusted decreases to int */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            result.len() as int == i as int,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] as int == 2 * (s@[j] as int)
        decreases (s.len() as int) - (i as int)
    {
        let s_i = s[i];
        let doubled_i64 = (s_i as i64) * 2;
        assert(doubled_i64 >= i32::MIN as i64 && doubled_i64 <= i32::MAX as i64);
        result.push(doubled_i64 as i32);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}