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
/* helper modified by LLM (iteration 4): proves sum non-negative for non-negative seq */
proof fn nonneg_sum_of_nonneg(s: Seq<int>)
    requires
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
    ensures
        sum(s) >= 0,
    decreases
        s.len()
{
    if s.len() == 0 {
        assert(sum(s) == 0);
        assert(sum(s) >= 0);
    } else {
        let tail = s.subrange(1, s.len() as int);
        nonneg_sum_of_nonneg(tail);
        assert(sum(s) == s[0] + sum(tail));
        assert(sum(tail) >= 0);
        assert(s[0] >= 0);
        assert(sum(s) >= 0);
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
    /* code modified by LLM (iteration 4): compute totals with native integers and construct greedy redistribution; then prove spec properties */
    let mut i: usize = 0usize;
    let mut total_i64: i64 = 0i64;
    while i < scores.len()
        invariant
            0 <= i as int && i as int <= scores.len() as int,
            total_i64 as int == sum(scores@.map(|_i: int, x: i8| x as int).subrange(0, i as int)),
        decreases
            scores.len() - i
    {
        total_i64 = total_i64 + (scores[i] as i64);
        i = i + 1usize;
    }

    let m_i64: i64 = m as i64;
    let result_i64: i64 = if total_i64 <= m_i64 { total_i64 } else { m_i64 };
    let result: i8 = result_i64 as i8;

    let mut redistributed: Vec<i8> = Vec::with_capacity(scores.len());
    redistributed.push(result);
    let mut rem_i64: i64 = total_i64 - result_i64;
    let mut j: usize = 1usize;
    while j < scores.len()
        invariant
            1 <= j as int && j as int <= scores.len() as int,
            rem_i64 as int >= 0,
            rem_i64 as int == total_i64 as int - sum(redistributed@.map(|_i: int, x: i8| x as int).subrange(0, j as int)),
        decreases
            scores.len() - j
    {
        let take_i64: i64 = if rem_i64 <= m_i64 { rem_i64 } else { m_i64 };
        redistributed.push(take_i64 as i8);
        rem_i64 = rem_i64 - take_i64;
        j = j + 1usize;
    }

    assert(rem_i64 == 0i64);

    proof {
        assert(total_i64 as int == sum(scores@.map(|_i: int, x: i8| x as int)));
        assert(redistributed.len() == scores.len());

        let mut p: usize = 0usize;
        while p < redistributed.len()
            invariant
                0 <= p as int && p as int <= redistributed.len() as int,
                forall|ii: int| 0 <= ii && ii < p as int ==> redistributed@.map(|_i: int, x: i8| x as int)[ii] >= 0 && redistributed@.map(|_i: int, x: i8| x as int)[ii] <= m as int,
            decreases
                redistributed.len() - p
        {
            let v: i8 = redistributed[p];
            assert((v as int) >= 0 && (v as int) <= m as int);
            p = p + 1usize;
        }

        assert(sum(redistributed@.map(|_i: int, x: i8| x as int)) == total_i64 as int);

        assert(redistributed@.map(|_i: int, x: i8| x as int)[0] == result_i64 as int);

        assert(exists|r: Seq<int>| valid_redistribution(scores@.map(|_i: int, x: i8| x as int), r, m as int) && r[0] == result_i64 as int);
    }

    result
}

// </vc-code>


}

fn main() {}