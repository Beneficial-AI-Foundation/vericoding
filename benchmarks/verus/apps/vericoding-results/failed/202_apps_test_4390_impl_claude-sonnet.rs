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
spec fn min_moves_lemma(a: int, b: int) -> bool
    recommends a > 0 && b > 0
{
    let result = (b - a % b) % b;
    result >= 0 && result < b && (a + result) % b == 0
}

/* helper modified by LLM (iteration 3): fixed lemma syntax */
proof fn proves_min_moves(a: int, b: int)
    requires a > 0 && b > 0
    ensures min_moves_lemma(a, b)
{
    let result = (b - a % b) % b;
    assert(a % b >= 0 && a % b < b);
    if a % b == 0 {
        assert(result == 0);
        assert((a + result) % b == a % b);
    } else {
        assert(result == b - a % b);
        assert(result > 0 && result < b);
        assert((a + result) % b == (a + b - a % b) % b);
        assert((a + b - a % b) % b == 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(test_cases: Vec<(i8, i8)>) -> (results: Vec<i8>)
    requires valid_input(test_cases@.map(|i, pair: (i8, i8)| (pair.0 as int, pair.1 as int)))
    ensures valid_output(test_cases@.map(|i, pair: (i8, i8)| (pair.0 as int, pair.1 as int)), results@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed ghost variable usage */
    let mut results = Vec::new();
    let mut i = 0;
    
    while i < test_cases.len()
        invariant
            i <= test_cases.len(),
            results.len() == i,
            valid_input(test_cases@.map(|j, pair: (i8, i8)| (pair.0 as int, pair.1 as int))),
            forall|j: int| 0 <= j < i ==> results@[j] as int == min_moves_to_divisible((test_cases@[j].0) as int, (test_cases@[j].1) as int),
            forall|j: int| 0 <= j < i ==> results@[j] as int >= 0,
        decreases test_cases.len() - i
    {
        let (a, b) = test_cases[i];
        
        proof {
            let a_int = a as int;
            let b_int = b as int;
            proves_min_moves(a_int, b_int);
        }
        
        let remainder = a % b;
        let moves = if remainder == 0 { 0 } else { b - remainder };
        
        results.push(moves);
        i += 1;
    }
    
    results
}
// </vc-code>


}

fn main() {}