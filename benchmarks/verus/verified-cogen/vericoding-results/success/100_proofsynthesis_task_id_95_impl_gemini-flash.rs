// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): No change as it was correct. */
fn min_usize(a: usize, b: usize) -> (res: usize) ensures (res == a || res == b) && res <= a && res <= b { if a < b { a } else { b } }
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
/* code modified by LLM (iteration 3): Added decreases clause to loop. */
{
    let mut min_len: usize = list[0].len();
    let mut i: usize = 1;
    while i < list.len()
        invariant
            0 < i && i <= list.len(),
            forall|k: int| 0 <= k < i as int ==> min_len <= #[trigger] list[k].len(),
            exists|j: int| 0 <= j < i as int && min_len == #[trigger] list[j].len(),
        decreases list.len() - i
    {
        min_len = min_usize(min_len, list[i].len());
        i = i + 1;
    }
    min_len
}
// </vc-code>

}
fn main() {}