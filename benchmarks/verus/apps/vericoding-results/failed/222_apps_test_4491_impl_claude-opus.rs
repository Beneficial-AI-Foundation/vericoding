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
/* helper modified by LLM (iteration 4): Added trigger annotations to fix quantifier inference */
proof fn sum_range_properties(s: Seq<int>, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
        forall|i: int| #![trigger s[i]] start <= i < end ==> s[i] >= 1,
    ensures
        sum_range(s, start, end) >= 0,
        start == end ==> sum_range(s, start, end) == 0,
        start < end ==> sum_range(s, start, end) == s[start] + sum_range(s, start + 1, end),
    decreases end - start
{
    if start >= end {
        assert(sum_range(s, start, end) == 0);
    } else {
        assert(sum_range(s, start, end) == s[start] + sum_range(s, start + 1, end));
        sum_range_properties(s, start + 1, end);
    }
}

proof fn sum_range_split(s: Seq<int>, start: int, mid: int, end: int)
    requires
        0 <= start <= mid <= end <= s.len(),
        forall|i: int| #![trigger s[i]] start <= i < end ==> s[i] >= 1,
    ensures
        sum_range(s, start, end) == sum_range(s, start, mid) + sum_range(s, mid, end),
    decreases end - start
{
    if start >= mid {
        assert(sum_range(s, start, mid) == 0);
    } else {
        assert(sum_range(s, start, mid) == s[start] + sum_range(s, start + 1, mid));
        assert(sum_range(s, start, end) == s[start] + sum_range(s, start + 1, end));
        sum_range_split(s, start + 1, mid, end);
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
    /* code modified by LLM (iteration 4): Added trigger annotations to fix quantifier inference error */
    let mut min_sum: i8 = 127;
    let mut i: usize = 0;
    
    while i < n as usize
        invariant
            0 <= i <= n as int,
            valid_input(n as int, a_1@.map_values(|x: i8| x as int), a_2@.map_values(|x: i8| x as int)),
            min_sum >= n + 1,
            min_sum <= 127,
            forall|j: int| #![trigger sum_range(a_1@.map_values(|x: i8| x as int), 0, j + 1)] 0 <= j < i ==> min_sum as int <= sum_range(a_1@.map_values(|x: i8| x as int), 0, j + 1) + sum_range(a_2@.map_values(|x: i8| x as int), j, n as int),
            i > 0 ==> exists|j: int| 0 <= j < i && min_sum as int == sum_range(a_1@.map_values(|x: i8| x as int), 0, j + 1) + sum_range(a_2@.map_values(|x: i8| x as int), j, n as int),
        decreases n as int - i as int
    {
        let mut sum1: i16 = 0;
        let mut j: usize = 0;
        
        while j <= i
            invariant
                0 <= j <= i + 1,
                j <= n as int,
                0 <= i < n as int,
                sum1 >= 0,
                sum1 <= (j as i16) * 100,
                sum1 as int == sum_range(a_1@.map_values(|x: i8| x as int), 0, j as int),
            decreases (i + 1) - j
        {
            proof {
                sum_range_properties(a_1@.map_values(|x: i8| x as int), 0, j as int);
                sum_range_properties(a_1@.map_values(|x: i8| x as int), 0, (j + 1) as int);
            }
            sum1 = sum1 + (a_1[j] as i16);
            j = j + 1;
        }
        
        let mut sum2: i16 = 0;
        j = i;
        
        while j < n as usize
            invariant
                i <= j <= n as int,
                0 <= i < n as int,
                sum2 >= 0,
                sum2 <= ((j - i) as i16) * 100,
                sum2 as int == sum_range(a_2@.map_values(|x: i8| x as int), i as int, j as int),
            decreases n as int - j as int
        {
            proof {
                sum_range_properties(a_2@.map_values(|x: i8| x as int), i as int, j as int);
                sum_range_properties(a_2@.map_values(|x: i8| x as int), i as int, (j + 1) as int);
            }
            sum2 = sum2 + (a_2[j] as i16);
            j = j + 1;
        }
        
        let current_sum = (sum1 + sum2) as i8;
        
        if i == 0 || current_sum < min_sum {
            min_sum = current_sum;
        }
        
        i = i + 1;
    }
    
    assert(exists|j: int| 0 <= j < n as int && min_sum as int == sum_range(a_1@.map_values(|x: i8| x as int), 0, j + 1) + sum_range(a_2@.map_values(|x: i8| x as int), j, n as int));
    assert(forall|j: int| #![trigger sum_range(a_1@.map_values(|x: i8| x as int), 0, j + 1)] 0 <= j < n as int ==> min_sum as int <= sum_range(a_1@.map_values(|x: i8| x as int), 0, j + 1) + sum_range(a_2@.map_values(|x: i8| x as int), j, n as int));
    
    min_sum
}
// </vc-code>


}

fn main() {}