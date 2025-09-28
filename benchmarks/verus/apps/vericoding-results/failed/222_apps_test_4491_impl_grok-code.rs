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
/* helper modified by LLM (iteration 5): fixed abs import and ensures order to resolve compilation errors */
fn sum_vec(v: &Vec<i8>, start: usize, end: usize) -> i32
    requires
        start <= end <= v.len(),
        forall|i: usize| start <= i < end ==> 1 <= v[i] && v[i] <= 100,
    ensures
        result == sum_range(v@.map_values(|x: i8| x as int), start as int, end as int),
        abs(result) <= 100 * (end - start) as i32,
{
    let mut sum = 0i32;
    let mut i = start;
    while i < end
        invariant
            start <= i <= end,
            sum == sum_range(v@.map_values(|x: i8| x as int), start as int, i as int),
            abs(sum) <= 100 * (i - start) as i32,
        decreases end - i
    {
        assert(abs(sum + v[i] as i32) <= 100 * ((i - start) + 1) as i32);
        sum += v[i] as i32;
        i += 1;
    }
    sum
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a_1: Vec<i8>, a_2: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a_1@.map_values(|x: i8| x as int), a_2@.map_values(|x: i8| x as int))
    ensures is_valid_result(n as int, a_1@.map_values(|x: i8| x as int), a_2@.map_values(|x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation by making ghost variables and using i32 casts */
    use vstd::math::abs;
    let n_int: ghost int = n as int;
    assert(n_int >= 1);
    let n_usize = n as usize;
    assert(n_usize as int == n_int);
    let a1_seq: ghost Seq<int> = a_1@.map_values(|x: i8| x as int);
    let a2_seq: ghost Seq<int> = a_2@.map_values(|x: i8| x as int);
    assert(a1_seq.len() == n_int && a2_seq.len() == n_int);
    let len1 = a_1.len();
    assert(len1 as int == a1_seq.len());
    assert(len1 == n_usize);
    let len2 = a_2.len();
    assert(len2 as int == a2_seq.len());
    assert(len2 == n_usize);
    let mut sum2_total: i32 = sum_vec(&a_2, 0, n_usize);
    assert(sum2_total == sum_range(a2_seq, 0, n_int));
    let mut sum1_cumulative: i32 = 0;
    let mut sum2: i32 = sum2_total;
    let mut max_sum: i32 = sum1_cumulative + sum2;
    let mut i = 0;
    while i < n_usize
        invariant
            0 <= i <= n_usize,
            sum1_cumulative == sum_range(a1_seq, 0, i as int),
            sum2 == sum_range(a2_seq, i as int, n_int),
            abs(sum1_cumulative) <= 100 * i as i32,
            abs(sum2) <= 100 * (n_usize - i) as i32,
            max_sum >= sum1_cumulative + sum2,
            forall|j: int| 0 <= j < i ==> max_sum >= sum_range(a1_seq, 0, j as int + 1) + sum_range(a2_seq, j as int, n_int),
        decreases n_usize - i
    {
        i += 1;
        sum1_cumulative += a_1[i - 1] as i32;
        let current_sum = sum1_cumulative + sum2;
        if current_sum > max_sum {
            max_sum = current_sum;
        }
        sum2 -= a_2[i - 1] as i32;
        assert(abs(sum1_cumulative) <= 100 * i as i32);
        assert(abs(sum2) <= 100 * (n_usize - i) as i32);
    }
    assert(valid_input(n_int, a1_seq, a2_seq));
    assert(max_sum as int >= n_int + 1);
    assert(max_sum as int <= (n_int + 1) * 100);
    (#[verifier::truncate] max_sum as i8)
}
// </vc-code>


}

fn main() {}