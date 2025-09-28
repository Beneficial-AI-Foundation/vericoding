// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(lst: Seq<int>) -> bool {
    5 <= lst.len() <= 10 &&
    forall|i: int| 0 <= i < lst.len() ==> #[trigger] lst[i] >= 1 && #[trigger] lst[i] <= 32
}

spec fn int_xor(a: int, b: int) -> int {
    let a_bv = a as u32;
    let b_bv = b as u32;
    (a_bv ^ b_bv) as int
}

spec fn min_of_sequence(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.len() == 1 {
        s[0]
    } else {
        let tail_min = min_of_sequence(s.skip(1));
        if s[0] <= tail_min {
            s[0]
        } else {
            tail_min
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): avoid map pattern issue with explicit sequence conversion */
spec fn sequence_from_vec(vec: Vec<i8>) -> Seq<int> {
    vec@
}

fn compute_min(lower: usize, upper: usize, vec: Vec<i8>) -> (min_val: i8)
    requires
        lower <= upper,
        upper < vec@.len(),
        forall|i: int| 0 <= i < vec@.len() ==> vec@[i] >= 1 && vec@[i] <= 32
    ensures
        min_val as int == min_of_sequence(sequence_from_vec(vec).subrange(lower as int, upper as int)),
    decreases upper - lower
{
    if lower == upper {
        vec[lower]
    } else {
        let mid = lower + ((upper - lower) / 2);
        let left_min = compute_min(lower, mid, vec);
        let right_min = compute_min(mid + 1, upper, vec);
        if left_min < right_min {
            left_min
        } else {
            right_min
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(lst: Vec<i8>) -> (result: i8)
    requires valid_input(lst@.map(|i: int, x: i8| x as int))
    ensures result as int == 2 + int_xor(lst@[2] as int, min_of_sequence(lst@.map(|i: int, x: i8| x as int)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use standard calculation without helper function */
    let vec_seq = lst@.map(|i: int, x: i8| x as int);
    let min_val = min_of_sequence(vec_seq);
    let xor_result = (lst[2] as u8) ^ (min_val as u8);
    (2 + xor_result as i8)
}
// </vc-code>


}

fn main() {}