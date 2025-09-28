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
/* helper modified by LLM (iteration 2): avoid using int in executable code */
fn compute_min_moves(a: i8, b: i8) -> (result: i8)
    requires a > 0 && b > 0
    ensures result == min_moves_to_divisible(a as int, b as int) as i8
{
    let remainder = a % b;
    let candidate = b - remainder;
    candidate % b
}
// </vc-helpers>

// <vc-spec>
fn solve(test_cases: Vec<(i8, i8)>) -> (results: Vec<i8>)
    requires valid_input(test_cases@.map(|i, pair: (i8, i8)| (pair.0 as int, pair.1 as int)))
    ensures valid_output(test_cases@.map(|i, pair: (i8, i8)| (pair.0 as int, pair.1 as int)), results@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): use usize for index and convert to int in ghost invariants */
{
    let mut results = Vec::new();
    let mut i: usize = 0;
    while i < test_cases.len()
        invariant
            0 <= (i as int) <= test_cases@.len(),
            results@.len() == (i as int),
            forall|j: int| 0 <= j < (i as int) ==> results@[j] == min_moves_to_divisible(test_cases@[j].0 as int, test_cases@[j].1 as int) as i8,
        decreases test_cases@.len() - (i as int)
    {
        let (a, b) = test_cases[i];
        let moves = compute_min_moves(a, b);
        results.push(moves);
        i += 1;
    }
    results
}
// </vc-code>


}

fn main() {}