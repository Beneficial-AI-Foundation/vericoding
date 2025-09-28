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
proof fn sum_range_monotonic(s: Seq<int>, start: int, end: int, i: int)
    requires
        0 <= start <= end <= s.len(),
        forall|k: int| #![trigger s[k]] start <= k < end ==> s[k] >= 1,
        start <= i <= end
    ensures
        sum_range(s, start, i) <= sum_range(s, start, end)
    decreases end - i
{
    if i < end {
        sum_range_monotonic(s, start, end, i + 1);
    }
}

proof fn sum_range_non_decreasing(s: Seq<int>, start: int, i: int, j: int)
    requires
        0 <= start <= i <= j <= s.len(),
        forall|k: int| #![trigger s[k]] start <= k < j ==> s[k] >= 1
    ensures
        sum_range(s, start, i) <= sum_range(s, start, j)
    decreases j - i
{
    if i < j {
        sum_range_non_decreasing(s, start, i, i + 1);
        sum_range_non_decreasing(s, start, i + 1, j);
    }
}

proof fn sum_range_partition(a: Seq<int>, i: int, j: int, k: int)
    requires
        0 <= i <= k <= j <= a.len(),
        forall|idx: int| #![trigger a[idx]] i <= idx < j ==> a[idx] >= 1
    ensures
        sum_range(a, i, j) == sum_range(a, i, k) + sum_range(a, k, j)
    decreases k - i
{
    if i < k {
        sum_range_partition(a, i + 1, j, k);
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
    /* code modified by LLM (iteration 5): fix compilation errors by converting sequences properly in proof context */
    ghost {
        let s1 = a_1@.map_values(|x: i8| x as int);
        let s2 = a_2@.map_values(|x: i8| x as int);
    }

    let mut min_val = 127i8;
    let mut prefix_sum = 0i8;
    let mut suffix_sum = 0i8;
    
    let mut k = n - 1;
    while k >= 0
        invariant
            -1 <= k <= n - 1,
            suffix_sum as int == sum_range(a_2@.map_values(|x: i8| x as int), (k + 1) as int, n as int)
        decreases (k + 1) as int
    {
        suffix_sum = suffix_sum + a_2[k as usize];
        k = k - 1;
    }
    
    let mut i = 0;
    let mut result = suffix_sum;
    
    while i < n
        invariant
            0 <= i <= n,
            prefix_sum as int == sum_range(a_1@.map_values(|x: i8| x as int), 0, i as int),
            suffix_sum as int == sum_range(a_2@.map_values(|x: i8| x as int), i as int, n as int),
            result as int >= n as int + 1,
            result as int <= (n as int + 1) * 100,
            exists|k: int| #![trigger sum_range(a_1@.map_values(|x: i8| x as int), 0, k + 1), sum_range(a_2@.map_values(|x: i8| x as int), k, n as int)] 0 <= k < i as int && result as int == sum_range(a_1@.map_values(|x: i8| x as int), 0, k + 1) + sum_range(a_2@.map_values(|x: i8| x as int), k, n as int),
            forall|k: int| #![trigger sum_range(a_1@.map_values(|x: i8| x as int), 0, k + 1), sum_range(a_2@.map_values(|x: i8| x as int), k, n as int)] 0 <= k < i as int ==> result as int <= sum_range(a_1@.map_values(|x: i8| x as int), 0, k + 1) + sum_range(a_2@.map_values(|x: i8| x as int), k, n as int)
        decreases n - i
    {
        prefix_sum = prefix_sum + a_1[i as usize];
        
        if i > 0 {
            suffix_sum = suffix_sum - a_2[(i - 1) as usize];
        }
        
        let total = prefix_sum + suffix_sum;
        if total < result {
            result = total;
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}