// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn min_second_value_first(s: &Vec<Vec<i32>>) -> (first_of_min_second: i32)
    requires 
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> s@[i].len() >= 2,
    ensures 
        exists|i: int| 0 <= i < s.len() && first_of_min_second == s@[i]@[0] && 
            (forall|j: int| 0 <= j < s.len() ==> s@[i]@[1] <= s@[j]@[1]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added invariant to propagate vector length precondition */
    let mut min_idx: usize = 0;
    let mut i: usize = 1;

    while i < s.len()
        invariant
            1 <= i <= s.len(),
            0 <= min_idx < i,
            forall|k: int| 0 <= k < s.len() ==> s@[k].len() >= 2,
            forall|j: int| 0 <= j < i ==> s@[min_idx as int]@[1] <= s@[j]@[1],
        decreases s.len() - i
    {
        if s[i][1] < s[min_idx][1] {
            min_idx = i;
        }
        i = i + 1;
    }

    s[min_idx][0]
}
// </vc-code>

}
fn main() {}