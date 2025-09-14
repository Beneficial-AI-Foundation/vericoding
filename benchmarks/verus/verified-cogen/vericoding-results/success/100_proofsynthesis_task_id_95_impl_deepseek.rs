// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

    spec fn min_usize(a: usize, b: usize) -> usize {
        if a < b { a } else { b }
    }

    proof fn min_le_bounds(a: usize, b: usize)
        ensures
            min_usize(a, b) <= a,
            min_usize(a, b) <= b,
    {
    }

    proof fn min_exists(a: usize, b: usize)
        ensures
            min_usize(a, b) == a || min_usize(a, b) == b,
    {
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
    let mut min = list[0].len();
    let mut i: usize = 1;
    
    while i < list.len()
        invariant
            i <= list.len(),
            min >= 0,
            forall|j: int| 0 <= j < i ==> min <= list[j].len(),
            exists|j: int| 0 <= j < i && min == list[j].len(),
        decreases list.len() - i,
    {
        let current_len = list[i].len();
        proof {
            min_le_bounds(min, current_len);
            min_exists(min, current_len);
        }
        min = if current_len < min { current_len } else { min };
        i += 1;
    }
    
    min
}
// </vc-code>

}
fn main() {}