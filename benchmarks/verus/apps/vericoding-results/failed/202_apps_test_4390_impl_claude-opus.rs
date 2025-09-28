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
    /* code modified by LLM (iteration 5): Added explicit bounds checks and assertions for preconditions */
    let mut results: Vec<i8> = Vec::new();
    let mut i = 0;
    
    while i < test_cases.len()
        invariant
            0 <= i <= test_cases.len(),
            results.len() == i,
            valid_input(test_cases@.map(|j, pair: (i8, i8)| (pair.0 as int, pair.1 as int))),
            forall|j: int| 0 <= j < i ==> results@[j] as int == min_moves_to_divisible(test_cases@[j].0 as int, test_cases@[j].1 as int),
            forall|j: int| 0 <= j < i ==> results@[j] >= 0,
        decreases test_cases.len() - i
    {
        let (a, b) = test_cases[i];
        
        proof {
            // Assert that the input is valid for this index
            assert(valid_input(test_cases@.map(|j, pair: (i8, i8)| (pair.0 as int, pair.1 as int))));
            assert(0 <= i < test_cases.len());
            let mapped = test_cases@.map(|j, pair: (i8, i8)| (pair.0 as int, pair.1 as int));
            assert(mapped[i as int].0 == test_cases@[i as int].0 as int);
            assert(mapped[i as int].1 == test_cases@[i as int].1 as int);
            assert(mapped[i as int].0 > 0 && mapped[i as int].1 > 0);
            assert(test_cases@[i as int].0 as int > 0);
            assert(test_cases@[i as int].1 as int > 0);
            assert(a as int > 0);
            assert(b as int > 0);
            assert(b != 0);
        }
        
        let remainder = a % b;
        let moves = if remainder == 0 {
            0i8
        } else {
            (b - remainder) as i8
        };
        
        proof {
            let a_int = a as int;
            let b_int = b as int;
            let remainder_int = remainder as int;
            let moves_int = moves as int;
            
            assert(a_int > 0 && b_int > 0);
            assert(remainder_int == a_int % b_int);
            assert(0 <= remainder_int < b_int);
            
            if remainder == 0 {
                assert(moves_int == 0);
                assert((b_int - a_int % b_int) % b_int == 0);
                assert(moves_int == (b_int - a_int % b_int) % b_int);
            } else {
                assert(remainder_int > 0);
                assert(moves_int == (b_int - remainder_int) as int);
                assert(b_int - remainder_int > 0);
                assert(b_int - remainder_int < b_int);
                assert((b_int - remainder_int) % b_int == b_int - remainder_int);
                assert(moves_int == (b_int - a_int % b_int) % b_int);
            }
            assert(moves_int == min_moves_to_divisible(a_int, b_int));
        }
        
        results.push(moves);
        i = i + 1;
    }
    
    proof {
        assert(results.len() == test_cases.len());
        assert forall|j: int| 0 <= j < results.len() implies
            results@[j] as int == min_moves_to_divisible(test_cases@[j].0 as int, test_cases@[j].1 as int) by {
            let mapped = test_cases@.map(|k, pair: (i8, i8)| (pair.0 as int, pair.1 as int));
            assert(mapped[j].0 == test_cases@[j].0 as int);
            assert(mapped[j].1 == test_cases@[j].1 as int);
            assert(mapped[j].0 > 0 && mapped[j].1 > 0);
            assert(results@[j] as int == min_moves_to_divisible(test_cases@[j].0 as int, test_cases@[j].1 as int));
        }
    }
    
    results
}
// </vc-code>


}

fn main() {}