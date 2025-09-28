// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, scores: Seq<int>) -> bool {
    n >= 1 && m >= 1 && scores.len() == n &&
    forall|i: int| 0 <= i < scores.len() ==> #[trigger] scores[i] >= 0 && #[trigger] scores[i] <= m
}

spec fn sum(nums: Seq<int>) -> int
    decreases nums.len()
{
    if nums.len() == 0 { 
        0 
    } else { 
        nums[0] + sum(nums.subrange(1, nums.len() as int)) 
    }
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

spec fn valid_redistribution(original: Seq<int>, redistributed: Seq<int>, m: int) -> bool {
    redistributed.len() == original.len() &&
    sum(redistributed) == sum(original) &&
    forall|i: int| 0 <= i < redistributed.len() ==> #[trigger] redistributed[i] >= 0 && #[trigger] redistributed[i] <= m
}

spec fn max_possible_first_score(n: int, m: int, scores: Seq<int>) -> int {
    min(sum(scores), m)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed nat literal syntax error */

fn lemma_sum_bounds(scores: Seq<int>, m: int)
    requires
        scores.len() >= 1,
        forall|i: int| 0 <= i < scores.len() ==> scores[i] >= 0 && scores[i] <= m,
    ensures
        sum(scores) >= 0,
        sum(scores) <= scores.len() * m,
    decreases scores.len()
{
    if scores.len() == 1 {
        assert(sum(scores) == scores[0]);
    } else {
        proof {
            let subrange = scores.subrange(1, scores.len() as int);
            lemma_sum_bounds(subrange, m);
        }
    }
}

fn lemma_redistribution_exists(scores: Seq<int>, m: int, target: int)
    requires
        scores.len() >= 1,
        forall|i: int| 0 <= i < scores.len() ==> scores[i] >= 0 && scores[i] <= m,
        target == min(sum(scores), m),
    ensures
        exists|redistributed: Seq<int>| valid_redistribution(scores, redistributed, m) && redistributed[0] == target,
{
    let total = sum(scores);
    if total <= m {
        let redistributed = seq![total].add(seq![0; (scores.len() - 1) as nat]);
        assert(redistributed.len() == scores.len());
        assert(sum(redistributed) == total);
        assert(redistributed[0] == total);
        assert(redistributed[0] == target);
    } else {
        let redistributed = seq![m].add(seq![0; (scores.len() - 1) as nat]);
        assert(redistributed.len() == scores.len());
        assert(redistributed[0] == m);
        assert(redistributed[0] == target);
    }
}

fn compute_sum(scores: &Vec<i8>) -> (result: i8)
    requires
        scores@.len() >= 1,
        forall|i: int| 0 <= i < scores@.len() ==> scores@[i] >= 0,
    ensures
        result as int == sum(scores@.map(|_i: int, x: i8| x as int)),
{
    let mut total: i8 = 0;
    let mut i = 0;
    
    while i < scores.len()
        invariant
            0 <= i <= scores.len(),
            total as int == sum(scores@.subrange(0, i as int).map(|_j: int, x: i8| x as int)),
    {
        total = total + scores[i];
        i = i + 1;
    }
    
    total
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, scores: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, m as int, scores@.map(|_i: int, x: i8| x as int)),
    ensures 
        result as int == max_possible_first_score(n as int, m as int, scores@.map(|_i: int, x: i8| x as int)),
        result as int == min(sum(scores@.map(|_i: int, x: i8| x as int)), m as int),
        exists|redistributed: Seq<int>| (valid_redistribution(scores@.map(|_i: int, x: i8| x as int), redistributed, m as int) && 
            redistributed[0] == result as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed nat literal syntax error */
    proof {
        lemma_sum_bounds(scores@.map(|_i: int, x: i8| x as int), m as int);
    }
    
    let total = compute_sum(&scores);
    let result = if total <= m { total } else { m };
    
    proof {
        lemma_redistribution_exists(scores@.map(|_i: int, x: i8| x as int), m as int, result as int);
    }
    
    result
}
// </vc-code>


}

fn main() {}