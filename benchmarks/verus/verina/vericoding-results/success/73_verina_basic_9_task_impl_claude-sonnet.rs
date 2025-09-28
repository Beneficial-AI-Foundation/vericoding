// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn has_common_element(a: &Vec<i32>, b: &Vec<i32>) -> (result: bool)
    requires 
        a.len() > 0,
        b.len() > 0,
    ensures
        result == (exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && a[i] == b[j]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed bounds checking by ensuring i and j are within bounds */
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            !(exists|x: int, y: int| 0 <= x < i && 0 <= y < b.len() && a[x] == b[y]),
        decreases a.len() - i
    {
        let mut j = 0;
        while j < b.len()
            invariant
                0 <= j <= b.len(),
                i < a.len(),
                !(exists|y: int| 0 <= y < j && a[i as int] == b[y]),
            decreases b.len() - j
        {
            if a[i] == b[j] {
                return true;
            }
            j += 1;
        }
        i += 1;
    }
    false
}
// </vc-code>

}
fn main() {}