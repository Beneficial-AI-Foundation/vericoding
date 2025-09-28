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
/* helper modified by LLM (iteration 5): fixed compilation error by correcting lemma path */
fn compute_moves(a: i8, b: i8) -> (moves: i8)
    requires
        a > 0,
        b > 0,
    ensures
        moves as int == min_moves_to_divisible(a as int, b as int),
        moves >= 0,
{
    let rem = a % b;
    let sub = b - rem;
    let moves = sub % b;
    proof {
        let a_int = a as int;
        let b_int = b as int;

        vstd::arithmetic::div_mod::lemma_rem_is_mod(a, b);
        assert(rem as int == a_int % b_int);

        assert(rem < b);
        assert(sub > 0);

        vstd::arithmetic::div_mod::lemma_rem_is_mod(sub, b);
        assert(moves as int == sub as int % b_int);

        assert(sub as int == b_int - rem as int);
        
        assert(moves as int == (b_int - rem as int) % b_int);
        assert(moves as int == (b_int - (a_int % b_int)) % b_int);
    }
    moves
}
// </vc-helpers>

// <vc-spec>
fn solve(test_cases: Vec<(i8, i8)>) -> (results: Vec<i8>)
    requires valid_input(test_cases@.map(|i, pair: (i8, i8)| (pair.0 as int, pair.1 as int)))
    ensures valid_output(test_cases@.map(|i, pair: (i8, i8)| (pair.0 as int, pair.1 as int)), results@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): confirmed loop logic is sound */
    let mut results: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    let ghost mapped_tcs = test_cases@.map(|_idx, p: (i8, i8)| (p.0 as int, p.1 as int));

    while i < test_cases.len()
        invariant
            0 <= i <= test_cases.len(),
            results.len() == i,
            test_cases.len() == mapped_tcs.len(),
            valid_input(mapped_tcs),
            forall|j: int| 0 <= j < i ==> (
                results@[j] as int == min_moves_to_divisible(
                    mapped_tcs@[j].0,
                    mapped_tcs@[j].1
                ) && results@[j] >= 0
            ),
        decreases test_cases.len() - i
    {
        let a = test_cases[i].0;
        let b = test_cases[i].1;

        proof {
            let p_int = (a as int, b as int);
            assert(p_int == mapped_tcs@[i as int]);
            assert(valid_input(mapped_tcs));
            assert(mapped_tcs@[i as int].0 > 0 && mapped_tcs@[i as int].1 > 0);
            assert(a > 0 && b > 0);
        }

        let moves = compute_moves(a, b);
        results.push(moves);
        
        i = i + 1;
    }
    results
}
// </vc-code>


}

fn main() {}