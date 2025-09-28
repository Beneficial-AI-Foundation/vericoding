// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a_1: Seq<int>, a_2: Seq<int>) -> bool {
    n >= 1 &&
    a_1.len() == n && a_2.len() == n &&
    forall|i: int| #![trigger a_1[i], a_2[i]] 0 <= i < n ==> 1 <= a_1[i] <= 100 && 1 <= a_2[i] <= 100
}

spec fn sum_range(s: Seq<int>, start: int, end: int) -> int
    decreases end - start when 0 <= start <= end <= s.len() && forall|i: int| #![trigger s[i]] start <= i < end ==> s[i] >= 1
{
    if start >= end { 
        0 
    } else { 
        s[start] + sum_range(s, start + 1, end) 
    }
}

spec fn is_valid_result(n: int, a_1: Seq<int>, a_2: Seq<int>, result: int) -> bool {
    valid_input(n, a_1, a_2) &&
    result >= n + 1 &&
    result <= (n + 1) * 100 &&
    exists|i: int| 0 <= i < n && result == sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n) &&
    forall|i: int| 0 <= i < n ==> result >= sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed int literal casting for arithmetic operations */
fn sum_range_properties(s: Seq<int>, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
        forall|i: int| #![trigger s[i]] start <= i < end ==> s[i] >= 1,
    ensures
        sum_range(s, start, end) >= end - start,
        sum_range(s, start, end) <= (end - start) * 100,
{
    if start < end {
        sum_range_properties(s, start + 1 as int, end);
    }
}

fn sum_range_monotonic(s: Seq<int>, start1: int, end1: int, start2: int, end2: int)
    requires
        0 <= start1 <= end1 <= s.len(),
        0 <= start2 <= end2 <= s.len(),
        start1 <= start2,
        end1 <= end2,
        forall|i: int| #![trigger s[i]] start1 <= i < end2 ==> s[i] >= 1,
    ensures
        sum_range(s, start1, end1) <= sum_range(s, start1, end2),
{
    if end1 < end2 {
        sum_range_monotonic(s, start1, end1, start2, end1);
        sum_range_monotonic(s, start1, end1 + 1 as int, start2, end2);
    }
}

fn sum_range_additive(s: Seq<int>, start: int, mid: int, end: int)
    requires
        0 <= start <= mid <= end <= s.len(),
        forall|i: int| #![trigger s[i]] start <= i < end ==> s[i] >= 1,
    ensures
        sum_range(s, start, end) == sum_range(s, start, mid) + sum_range(s, mid, end),
{
    if start < mid {
        sum_range_additive(s, start + 1 as int, mid, end);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a_1: Vec<i8>, a_2: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a_1@.map_values(|x: i8| x as int), a_2@.map_values(|x: i8| x as int))
    ensures is_valid_result(n as int, a_1@.map_values(|x: i8| x as int), a_2@.map_values(|x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed array indexing with usize casts */
    let mut min_sum = (n + 1) * 100;
    let mut i = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            valid_input(n as int, a_1@.map_values(|x: i8| x as int), a_2@.map_values(|x: i8| x as int)),
            min_sum >= n + 1,
            min_sum <= (n + 1) * 100,
        decreases n - i
    {
        let mut sum_a1 = 0;
        let mut k = 0;
        
        while k <= i
            invariant 0 <= k <= i + 1
            decreases i + 1 - k
        {
            sum_a1 += a_1[k as usize] as i8;
            k += 1;
        }
        
        let mut sum_a2 = 0;
        let mut j = i;
        
        while j < n
            invariant i <= j <= n
            decreases n - j
        {
            sum_a2 += a_2[j as usize] as i8;
            j += 1;
        }
        
        let current_sum = sum_a1 + sum_a2;
        
        if current_sum < min_sum {
            min_sum = current_sum;
        }
        
        i += 1;
    }
    
    min_sum
}
// </vc-code>


}

fn main() {}