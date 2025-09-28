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

proof fn lemma_mod_properties_nonnegative(a: int, b: int)
    requires
        a > 0,
        b > 0,
    ensures
        a % b >= 0,
        a % b < b,
{
    vstd::arithmetic::div_mod::mod_bounds(a, b);
}

proof fn lemma_mod_properties_subtract(a: int, b: int)
    requires
        a > 0,
        b > 0,
    ensures
        (b - a % b) % b >= 0,
        (b - a % b) % b < b,
{
    let rem = a % b;
    vstd::arithmetic::div_mod::mod_bounds(a, b);
    if rem < b {
        let diff = b - rem;
        vstd::arithmetic::div_mod::mod_bounds(diff, b);
    }
}

proof fn lemma_min_moves_correctness(a: int, b: int)
    requires
        a > 0,
        b > 0,
    ensures
        min_moves_to_divisible(a, b) == (b - a % b) % b,
{
    lemma_mod_properties_nonnegative(a, b);
    lemma_mod_properties_subtract(a, b);
}

// </vc-helpers>

// <vc-spec>
fn solve(test_cases: Vec<(i8, i8)>) -> (results: Vec<i8>)
    requires valid_input(test_cases@.map(|i, pair: (i8, i8)| (pair.0 as int, pair.1 as int)))
    ensures valid_output(test_cases@.map(|i, pair: (i8, i8)| (pair.0 as int, pair.1 as int)), results@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation errors by using correct mod_bounds function */
    let mut results = Vec::new();
    let mut i: usize = 0;
    
    while i < test_cases.len()
        invariant
            i <= test_cases.len(),
            results@.len() == i,
            valid_output(test_cases@.map(|j, pair: (i8, i8)| (pair.0 as int, pair.1 as int)).subrange(0, i as int), results@.map(|j, x: i8| x as int)),
    {
        let (a, b) = test_cases[i];
        proof {
            lemma_min_moves_correctness(a as int, b as int);
        }
        let moves = ((b - a % b) % b) as i8;
        results.push(moves);
        i += 1;
    }
    
    results
}
// </vc-code>


}

fn main() {}