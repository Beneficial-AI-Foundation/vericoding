// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed arithmetic overflow and termination */
fn find_max_index(a: &Vec<i8>, start: usize, end: usize) -> (result: usize)
    requires 0 <= start < end <= a.len(),
    ensures start <= result < end,
        forall|j: int| start as int <= j < end as int ==> a@[j] <= a@[result as int],
        forall|j: int| start as int <= j < end as int && a@[j] == a@[result as int] ==> result <= j as usize,
    decreases end - start,
{
    if start + 1 == end {
        start
    } else {
        let mid = start + (end - start) / 2;
        let left_max = find_max_index(a, start, mid);
        let right_max = find_max_index(a, mid, end);
        if a[left_max] >= a[right_max] {
            left_max
        } else {
            right_max
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn argmax(a: Vec<i8>) -> (result: usize)
    requires a.len() > 0,
    ensures 
        result < a.len(),
        forall|j: int| 0 <= j < a@.len() ==> a@[j] <= a@[result as int],
        forall|j: int| 0 <= j < a@.len() && a@[j] == a@[result as int] ==> result <= j as usize,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): updated iteration number */
{
    find_max_index(&a, 0, a.len())
}
// </vc-code>

}
fn main() {}