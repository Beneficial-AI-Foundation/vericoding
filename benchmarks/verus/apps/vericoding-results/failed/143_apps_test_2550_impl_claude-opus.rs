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
/* helper modified by LLM (iteration 3): Fixed proof function to not use while loops */
proof fn sum_subrange_lemma(nums: Seq<int>, start: int, end: int)
    requires
        0 <= start <= end <= nums.len(),
    ensures
        sum(nums.subrange(start, end)) == sum(nums.subrange(start, end)),
    decreases end - start
{
    if start == end {
        assert(nums.subrange(start, end).len() == 0);
    } else {
        sum_subrange_lemma(nums, start + 1, end);
    }
}

proof fn sum_redistribute_lemma(scores: Seq<int>, m: int)
    requires
        scores.len() >= 1,
        forall|i: int| 0 <= i < scores.len() ==> scores[i] >= 0 && scores[i] <= m,
    ensures
        exists|redistributed: Seq<int>| 
            redistributed.len() == scores.len() &&
            sum(redistributed) == sum(scores) &&
            forall|i: int| 0 <= i < redistributed.len() ==> redistributed[i] >= 0 && redistributed[i] <= m &&
            redistributed[0] == min(sum(scores), m),
{
    let total = sum(scores);
    let first_val = min(total, m);
    let remaining = total - first_val;
    
    // Construct the redistributed sequence directly
    let redistributed = if scores.len() == 1 {
        seq![first_val]
    } else if scores.len() == 2 {
        seq![first_val, remaining]
    } else {
        // For longer sequences, put first_val first and distribute the rest
        let mut result = seq![first_val];
        let mut left = remaining;
        let mut idx = 1;
        
        // Build sequence recursively
        result = build_redistribution(result, left, scores.len() as int, m, idx);
        result
    };
    
    assert(redistributed.len() == scores.len());
    assert(sum(redistributed) == sum(scores));
    assert(redistributed[0] == first_val);
}

// Helper to build redistribution sequence
spec fn build_redistribution(current: Seq<int>, leftover: int, target_len: int, m: int, idx: int) -> Seq<int>
    decreases target_len - idx
{
    if idx >= target_len {
        current
    } else if idx == target_len - 1 {
        current.push(leftover)
    } else {
        let to_add = if leftover <= m { leftover } else { m };
        build_redistribution(current.push(to_add), leftover - to_add, target_len, m, idx + 1)
    }
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
    /* code modified by LLM (iteration 3): Added decreases clause to while loop */
    let mut total: i8 = 0;
    let mut i: usize = 0;
    
    while i < scores.len()
        invariant
            i <= scores.len(),
            total as int == sum(scores@.map(|_j: int, x: i8| x as int).subrange(0, i as int)),
            forall|j: int| 0 <= j < i ==> scores@.map(|_k: int, x: i8| x as int)[j] >= 0,
            forall|j: int| 0 <= j < i ==> scores@.map(|_k: int, x: i8| x as int)[j] <= m as int,
        decreases scores.len() - i
    {
        total = total + scores[i];
        i = i + 1;
    }
    
    assert(total as int == sum(scores@.map(|_i: int, x: i8| x as int)));
    
    proof {
        sum_redistribute_lemma(scores@.map(|_i: int, x: i8| x as int), m as int);
    }
    
    let result = if total <= m { total } else { m };
    
    assert(result as int == min(sum(scores@.map(|_i: int, x: i8| x as int)), m as int));
    assert(result as int == max_possible_first_score(n as int, m as int, scores@.map(|_i: int, x: i8| x as int)));
    
    result
}
// </vc-code>


}

fn main() {}