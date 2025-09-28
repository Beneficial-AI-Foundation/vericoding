// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(test_cases: Seq<(int, int)>) -> bool {
    forall|i: int| 0 <= i < test_cases.len() ==> 
        test_cases[i].0 > 0 && test_cases[i].1 > 0
}

spec fn min_moves_to_divisible(a: int, b: int) -> int
    recommends a > 0 && b > 0
{
    (b - a % b) % b
}

spec fn valid_output(test_cases: Seq<(int, int)>, results: Seq<int>) -> bool
    recommends valid_input(test_cases)
{
    results.len() == test_cases.len() &&
    forall|i: int| 0 <= i < results.len() ==> 
        results[i] == min_moves_to_divisible(test_cases[i].0, test_cases[i].1) &&
        results[i] >= 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers are needed, so removed the comment */

// </vc-helpers>

// <vc-spec>
fn solve(test_cases: Vec<(i8, i8)>) -> (results: Vec<i8>)
    requires valid_input(test_cases@.map(|i, pair: (i8, i8)| (pair.0 as int, pair.1 as int)))
    ensures valid_output(test_cases@.map(|i, pair: (i8, i8)| (pair.0 as int, pair.1 as int)), results@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type casting from `i8` to `int` by wrapping in `ghost` blocks. */
{
    let mut results: Vec<i8> = Vec::new();
    let mut i = 0;

    while i < test_cases.len()
        invariant // `i` is a valid index into `test_cases` not past `results.len()`
            0 <= i,
            i <= test_cases.len(),
            results.len() == i,
            // Each element added to `results` satisfies the output condition for its corresponding test case.
            forall|j: int| 0 <= j < i ==> {
                let tc_j_a: int = test_cases@[j].0 as int;
                let tc_j_b: int = test_cases@[j].1 as int;
                let result_j: int = results@[j] as int;
                result_j == min_moves_to_divisible(tc_j_a, tc_j_b) && result_j >= 0
            },
            // The input validity holds throughout the loop.
            valid_input(test_cases@.map(|k, pair: (i8, i8)| (pair.0 as int, pair.1 as int)))
        decreases test_cases.len() - i
    {
        let (a_i8, b_i8) = test_cases[i];
        
        let ghost a: int = a_i8 as int;
        let ghost b: int = b_i8 as int;

        proof {
            assert(valid_input(test_cases@.map(|k, pair: (i8, i8)| (pair.0 as int, pair.1 as int))));
            assert(0 <= (i as int) && (i as int) < test_cases.len());
            assert(test_cases@[i as int].0 as int > 0 && test_cases@[i as int].1 as int > 0);
        }

        let moves = min_moves_to_divisible(a, b);
        results.push(moves as i8);
        i = i + 1;
    }
    results
}
// </vc-code>


}

fn main() {}