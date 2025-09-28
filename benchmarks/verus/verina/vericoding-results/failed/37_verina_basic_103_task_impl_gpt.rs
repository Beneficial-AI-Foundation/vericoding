// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove indices 4 and 7 are within bounds when len >= 8 */
proof fn lemma_len_ge_8_implies_bounds(len: usize)
    requires len >= 8,
    ensures
        4 < len,
        7 < len,
{
    assert(len >= 8);
    assert(4 < len); // since len >= 8 > 4
    assert(7 < len); // since len >= 8 > 7
}
// </vc-helpers>

// <vc-spec>
fn update_elements(a: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() >= 8,
    ensures
        result[4] == a[4] + 3,
        result[7] == 516,
        forall|i: int| 0 <= i < a.len() && i != 4 && i != 7 ==> result[i] == a[i],
        result.len() == a.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): copy elements, then update index 4 by +3 (exact add) and set index 7 to 516 */
    let mut r: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            r.len() == i,
            forall|j: int| 0 <= j < i as int ==> r[j] == a[j],
        decreases a.len() - i
    {
        let v = a[i];
        r.push(v);
        i = i + 1;
    }
    proof { lemma_len_ge_8_implies_bounds(a.len()); }
    r[4] = r[4] + 3;
    r[7] = 516;
    r
}
// </vc-code>

}
fn main() {}