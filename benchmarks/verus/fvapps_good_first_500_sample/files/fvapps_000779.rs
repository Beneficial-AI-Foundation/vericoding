// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn confidence_sum(conf: Seq<int>) -> int
    decreases conf.len()
{
    if conf.len() == 0 {
        0
    } else {
        conf[0] + confidence_sum(conf.skip(1))
    }
}

spec fn count_problems_with_at_least_two_confident(confidence_matrix: Seq<Vec<int>>) -> int
    decreases confidence_matrix.len()
{
    if confidence_matrix.len() == 0 {
        0
    } else {
        let first_sum = confidence_sum(confidence_matrix[0]@);
        let rest_count = count_problems_with_at_least_two_confident(confidence_matrix.skip(1));
        if first_sum >= 2 {
            1 + rest_count
        } else {
            rest_count
        }
    }
}

fn count_solved_problems(n: usize, confidence_matrix: Vec<Vec<i32>>) -> (result: usize)
    requires 
        n >= 1,
        n <= 1000,
        confidence_matrix.len() == n,
        forall|i: int| 0 <= i < confidence_matrix.len() ==> confidence_matrix[i].len() == 3,
        forall|i: int, j: int| 0 <= i < confidence_matrix.len() && 0 <= j < 3 ==> 
            (confidence_matrix[i][j] == 0 || confidence_matrix[i][j] == 1),
    ensures
        result <= confidence_matrix.len(),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {
    // let test_matrix = vec![vec![1, 1, 0], vec![1, 1, 1], vec![1, 0, 0]];
    // let result = count_solved_problems(3, test_matrix);
    // println!("{}", result);
}