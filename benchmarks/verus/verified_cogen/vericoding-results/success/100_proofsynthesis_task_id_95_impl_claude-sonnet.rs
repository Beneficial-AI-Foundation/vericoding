// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn min_of_two(a: usize, b: usize) -> usize { if a <= b { a } else { b } }

proof fn min_properties(a: usize, b: usize)
    ensures
        min_of_two(a, b) <= a,
        min_of_two(a, b) <= b,
        min_of_two(a, b) == a || min_of_two(a, b) == b,
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
    /* code modified by LLM (iteration 4): fixed type casting for min_index */
    let mut min = list[0].len();
    let mut min_index = 0;
    
    for i in 1..list.len()
        invariant
            min >= 0,
            0 <= min_index < list.len(),
            min == list[min_index as int].len(),
            forall|j: int| 0 <= j < i ==> min <= list[j].len(),
    {
        if list[i].len() < min {
            min = list[i].len();
            min_index = i;
        }
    }
    
    min
}
// </vc-code>

}
fn main() {}