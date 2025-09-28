// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(angles: Seq<int>) -> bool {
    forall|i: int| 0 <= i < angles.len() ==> #[trigger] angles[i] >= 1 && #[trigger] angles[i] < 180
}

spec fn gcd(a: int, b: int) -> int;

spec fn compute_answer(angle: int) -> int {
    let g = gcd(angle, 180int);
    let de_over_g = angle / g;
    let n180_over_g = 180int / g;
    if de_over_g == n180_over_g - 1 { n180_over_g * 2 } else { n180_over_g }
}

spec fn correct_output(angles: Seq<int>, result: Seq<int>) -> bool {
    valid_input(angles) ==> (
        result.len() == angles.len() &&
        forall|i: int| 0 <= i < angles.len() ==> #[trigger] result[i] == compute_answer(#[trigger] angles[i])
    )
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added `uninterp` keyword to `gcd` spec function for proper verification. */
uninterp spec fn gcd(a: int, b: int) -> int;
// </vc-helpers>

// <vc-spec>
fn solve(angles: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(angles@.map(|i, x: i8| x as int))
    ensures correct_output(angles@.map(|i, x: i8| x as int), result@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type casting of `computed_val` to `i8` by asserting compute_answer result range. */
{
    let mut result_vec: Vec<i8> = Vec::new();
    let angles_seq: Seq<int> = angles@.map(|x: i8| x as int);

    let mut i: int = 0;
    while i < angles_seq.len()
        invariant
            0 <= i,
            i <= angles_seq.len(),
            result_vec@.len() == i,
            forall|j: int| 0 <= j < i ==> result_vec@[j] == compute_answer(angles_seq[j]) as i8,
        decreases angles_seq.len() - i
    {
        let angle: int = angles_seq[i];
        let computed_val: int = compute_answer(angle);
        /* Verus requires proof that `computed_val` fits within `i8` range */
        // The problem statement implies all angles and results will be within 1 to 180 (so i8 is fine)
        assert(computed_val >= 1 && computed_val <= 2 * 180);
        result_vec.push(computed_val as i8);
        i = i + 1;
    }

    result_vec
}
// </vc-code>


}

fn main() {}