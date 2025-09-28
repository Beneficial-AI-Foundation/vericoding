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

// </vc-helpers>

// <vc-spec>
fn solve(test_cases: Vec<(i8, i8)>) -> (results: Vec<i8>)
    requires valid_input(test_cases@.map(|i, pair: (i8, i8)| (pair.0 as int, pair.1 as int)))
    ensures valid_output(test_cases@.map(|i, pair: (i8, i8)| (pair.0 as int, pair.1 as int)), results@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added assertions and invariant clauses to satisfy preconditions and recommendations */
    let mut results = Vec::new();
    let mut i: usize = 0;
    while i < test_cases.len()
        invariant
            results.len() == i,
            forall|j: int| 0 <= j < i as int ==> 
                test_cases@[j].0 as int > 0 && test_cases@[j].1 as int > 0,
            forall|j: int| 0 <= j < i as int ==> results@[j] as int == min_moves_to_divisible(test_cases@[j].0 as int, test_cases@[j].1 as int),
        decreases (test_cases.len() - i) as int
    {
        let (a, b) = test_cases[i];
        let a_i32 = a as i32;
        let b_i32 = b as i32;
        assert(a_i32 >= 1 && b_i32 >= 1);
        let rem = a_i32 % b_i32;
        let moves_i32 = if rem == 0 { 0 } else { b_i32 - rem };
        assert(moves_i32 < 128);
        let moves_i8 = moves_i32 as i8;
        results.push(moves_i8);
        i += 1;
    }
    results
}
// </vc-code>


}

fn main() {}