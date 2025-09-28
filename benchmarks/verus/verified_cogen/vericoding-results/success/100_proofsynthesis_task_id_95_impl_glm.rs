// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min_usize(a: usize, b: usize) -> usize {
    if a < b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn smallest_list_length(list: &Vec<Vec<i32>>) -> (min: usize)

    requires
        list.len() > 0,

    ensures
        min >= 0,
        forall|i: int| 0 <= i < list.len() ==> min <= #[trigger] list[i].len(),
        exists|i: int| 0 <= i < list.len() && min == #[trigger] list[i].len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed loop invariant by starting at i=1 */
    let mut min = list[0].len();
    let mut i = 1;
    while i < list.len()
        invariant
            1 <= i <= list.len(),
            min >= 0,
            forall|j: int| 0 <= j < i ==> min <= #[trigger] list[j].len(),
            exists|j: int| 0 <= j < i && min == #[trigger] list[j].len()
        decreases list.len() - i
    {
        if list[i].len() < min {
            min = list[i].len();
        }
        i += 1;
    }
    min
}
// </vc-code>

}
fn main() {}