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
/* helper modified by LLM (iteration 5): no changes */
proof fn lemma_sum_range_split(s: Seq<int>, start: int, mid: int, end: int)
    requires
        0 <= start <= mid <= end <= s.len(),
        forall|i: int| #![trigger s[i]] start <= i < end ==> s[i] >= 1,
    ensures
        sum_range(s, start, end) == sum_range(s, start, mid) + sum_range(s, mid, end),
    decreases end - start
{
    if start < mid {
        lemma_sum_range_split(s, start + 1, mid, end);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a_1: Vec<i8>, a_2: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a_1@.map_values(|x: i8| x as int), a_2@.map_values(|x: i8| x as int))
    ensures is_valid_result(n as int, a_1@.map_values(|x: i8| x as int), a_2@.map_values(|x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed type errors by using ghost variables for int/nat types */
{
    let ghost n_int: int = n as int;
    let ghost a_1_seq = a_1@.map_values(|x: i8| x as int);
    let ghost a_2_seq = a_2@.map_values(|x: i8| x as int);

    let mut ghost min_sum_ghost: int = (n_int + 1) * 100 + 100; // Initialize with a value larger than any possible sum

    let mut k: i8 = 0;
    while (k as int) < n_int
        invariant
            0 <= (k as int) <= n_int,
            forall|j: int| 0 <= j < (k as int) ==> min_sum_ghost <= sum_range(a_1_seq, 0, j + 1) + sum_range(a_2_seq, j, n_int),
            min_sum_ghost >= n_int + 1,
            min_sum_ghost <= (n_int + 1) * 100 + 100,
    {
        let ghost current_a1_sum = sum_range(a_1_seq, 0, (k as int) + 1);
        let ghost current_a2_sum = sum_range(a_2_seq, (k as int), n_int);
        let ghost current_total_sum = current_a1_sum + current_a2_sum;

        if current_total_sum < min_sum_ghost {
            min_sum_ghost = current_total_sum;
        }

        k = k + 1;
    }

    // Proof to show that the initial min_sum is greater than any possible sum, so it will be updated.
    // Since 1 <= a[i] <= 100, the minimum possible sum_range(a_1_seq, 0, j + 1) is (j+1)*1.
    // The minimum possible sum_range(a_2_seq, j, n_int) is (n_int - j)*1.
    // So, current_total_sum >= (j+1) + (n_int - j) = n_int + 1.
    // The maximum possible sum is (j+1)*100 + (n_int-j)*100 = (n_int+1)*100.
    proof {
        assert forall|i: int| 0 <= i < n_int implies 1 <= a_1_seq[i] <= 100 && 1 <= a_2_seq[i] <= 100 by { }
        // The original lambda for sum range split was missing the arguments for len for a_1_seq and a_2_seq, removed a_1_seq from here since it has to pass by one argument
        lemma_sum_range_split(a_1_seq, 0, 0, n_int);
        lemma_sum_range_split(a_2_seq, 0, 0, n_int);

        assert(sum_range(a_1_seq, 0, 0 + 1) + sum_range(a_2_seq, 0, n_int) <= (n_int + 1) * 100);
        assert(sum_range(a_1_seq, 0, 0 + 1) + sum_range(a_2_seq, 0, n_int) >= n_int + 1) ;
        assert(min_sum_ghost > sum_range(a_1_seq, 0, 0 + 1) + sum_range(a_2_seq, 0, n_int));
    }

    min_sum_ghost as i8
}
// </vc-code>


}

fn main() {}