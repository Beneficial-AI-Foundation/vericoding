// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 2): Added decreases clause to fix loop verification */
    let mut min = list[0].len();
    let mut i = 1;
    while i < list.len()
        invariant
            0 <= i <= list.len(),
            forall|j: int| 0 <= j < i ==> min <= list[j].len(),
            exists|j: int| 0 <= j < i && min == list[j].len(),
        decreases list.len() - i
    {
        if list[i].len() < min {
            min = list[i].len();
        }
        i = i + 1;
    }
    min
}
// </vc-code>

}
fn main() {}