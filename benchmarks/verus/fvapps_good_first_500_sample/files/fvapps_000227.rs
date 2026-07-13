// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn contains_positive(xs: Seq<i32>, val: i32) -> bool {
    exists|i: int| 0 <= i < xs.len() && xs[i] == val && val > 0
}

spec fn all_positives_below(xs: Seq<i32>, bound: i32) -> bool {
    forall|i: i32| 1 <= i < bound ==> contains_positive(xs, i)
}

spec fn seq_from_vec(v: Vec<i32>) -> Seq<i32>;

fn find_first_missing_positive(xs: Vec<i32>) -> (result: u32)
    ensures 
        result > 0,
        !contains_positive(seq_from_vec(xs), result as i32),
        all_positives_below(seq_from_vec(xs), result as i32),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    1
    // impl-end
}
// </vc-code>


}
fn main() {
    // Apps difficulty: interview
    // Assurance level: guarded_and_plausible

    // let result1 = find_first_missing_positive(vec![1, 2, 0]);
    // assert_eq!(result1, 3);

    // let result2 = find_first_missing_positive(vec![3, 4, -1, 1]);
    // assert_eq!(result2, 2);

    // let result3 = find_first_missing_positive(vec![7, 8, 9, 11, 12]);
    // assert_eq!(result3, 1);
}