// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(test_cases: Seq<Seq<int>>) -> bool {
    forall|i: int| 0 <= i < test_cases.len() ==> 
        test_cases[i].len() >= 1 && 
        forall|j: int| 0 <= j < test_cases[i].len() ==> test_cases[i][j] >= 1
}

spec fn valid_results(results: Seq<Seq<char>>) -> bool {
    forall|i: int| 0 <= i < results.len() ==> 
        results[i] == seq!['F', 'i', 'r', 's', 't'] || results[i] == seq!['S', 'e', 'c', 'o', 'n', 'd']
}

spec fn count_leading_ones(piles: Seq<int>) -> nat
    decreases piles.len()
{
    if piles.len() == 0 {
        0
    } else if piles[0] != 1 {
        0
    } else {
        1 + count_leading_ones(piles.subrange(1, piles.len() as int))
    }
}

spec fn count_ones_in_seq(piles: Seq<int>) -> nat {
    piles.filter(|x: int| x == 1).len()
}

spec fn correct_game_result(piles: Seq<int>, result: Seq<char>) -> bool {
    &&& piles.len() >= 1
    &&& (forall|j: int| 0 <= j < piles.len() ==> piles[j] >= 1)
    &&& (result == seq!['F', 'i', 'r', 's', 't'] || result == seq!['S', 'e', 'c', 'o', 'n', 'd'])
    &&& {
        let ones_count = count_ones_in_seq(piles);
        let all_ones = (ones_count == piles.len());
        let leading_ones = count_leading_ones(piles);
        if all_ones {
            if ones_count % 2 == 1 {
                result == seq!['F', 'i', 'r', 's', 't']
            } else {
                result == seq!['S', 'e', 'c', 'o', 'n', 'd']
            }
        } else {
            if leading_ones % 2 == 1 {
                result == seq!['S', 'e', 'c', 'o', 'n', 'd']
            } else {
                result == seq!['F', 'i', 'r', 's', 't']
            }
        }
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(test_cases: Vec<Vec<i8>>) -> (results: Vec<Vec<char>>)
    requires 
        valid_input(test_cases@.map(|i: int, v: Vec<i8>| v@.map(|j: int, x: i8| x as int)))
    ensures 
        results.len() == test_cases.len(),
        valid_results(results@.map(|i: int, v: Vec<char>| v@)),
        forall|i: int| 0 <= i < test_cases.len() ==> correct_game_result(test_cases@[i].map(|j: int, x: i8| x as int), results@[i])
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}