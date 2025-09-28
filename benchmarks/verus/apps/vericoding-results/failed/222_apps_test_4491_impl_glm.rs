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
/* helper modified by LLM (iteration 2): removed top-level proof block and kept helper functions */
fn lemma_sum_range_non_decreasing(n: int, s: Seq<int>)
    requires
        n >= 1,
        s.len() == n,
        forall|i: int| 0 <= i < n ==> 1 <= s[i] <= 100
    ensures
        forall|i: int, j: int| 0 <= i <= j <= n ==> sum_range(s, 0, i) <= sum_range(s, 0, j)
{
    reveal(sum_range);
    assert forall|i: int, j: int| 0 <= i <= j <= n implies sum_range(s, 0, i) <= sum_range(s, 0, j) by {
        if i == j {
            assert(sum_range(s, 0, i) == sum_range(s, 0, j));
        } else {
            calc! {
                sum_range(s, 0, i);
                <= { assert(sum_range(s, 0, j) == sum_range(s, 0, i) + sum_range(s, i, j)); }
                sum_range(s, 0, i) + sum_range(s, i, j);
                == { assert(sum_range(s, i, j) >= 0); }
                sum_range(s, 0, j);
            }
        }
    }
}

fn compute_min_value(n: int, a_1: Seq<int>, a_2: Seq<int>) -> (result: int)
    requires
        valid_input(n, a_1, a_2)
    ensures
        result >= n + 1,
        result <= (n + 1) * 100,
        exists|i: int| 0 <= i < n && result == sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n),
        forall|i: int| 0 <= i < n ==> result >= sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n)
{
    let mut min_value = sum_range(a_1, 0, n) + sum_range(a_2, 0, n);
    let mut best_i = 0;
    
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            min_value >= n + 1,
            min_value <= (n + 1) * 100,
            exists|j: int| 0 <= j < i && min_value == sum_range(a_1, 0, j + 1) + sum_range(a_2, j, n),
            forall|j: int| 0 <= j < i ==> min_value <= sum_range(a_1, 0, j + 1) + sum_range(a_2, j, n),
            forall|j: int| 0 <= j < n ==> min_value >= sum_range(a_1, 0, j + 1) + sum_range(a_2, j, n)
        decreases n - i
    {
        let current_value = sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n);
        if current_value < min_value {
            min_value = current_value;
            best_i = i;
        }
        i = i + 1;
    }
    
    min_value
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a_1: Vec<i8>, a_2: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a_1@.map_values(|x: i8| x as int), a_2@.map_values(|x: i8| x as int))
    ensures is_valid_result(n as int, a_1@.map_values(|x: i8| x as int), a_2@.map_values(|x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): implemented the logic using compute_min_value helper, but note potential overflow for large n */
{
    let n_int = n as int;
    let a_1_int = a_1@.map_values(|x: i8| x as int);
    let a_2_int = a_2@.map_values(|x: i8| x as int);
    
    let result_int = compute_min_value(n_int, a_1_int, a_2_int);
    
    result_int as i8
}
// </vc-code>


}

fn main() {}