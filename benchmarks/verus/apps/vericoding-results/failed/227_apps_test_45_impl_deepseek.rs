// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int) -> bool
{
    n > 0 && k > 0
}

spec fn is_strictly_increasing(s: Seq<int>) -> bool
{
    forall|i: int| 0 <= i < s.len() - 1 ==> #[trigger] s[i] < s[i+1]
}

spec fn all_positive(s: Seq<int>) -> bool
{
    forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] > 0
}

spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum_seq(s.subrange(1, s.len() as int)) }
}

spec fn valid_sequence(s: Seq<int>, n: int, k: int) -> bool
{
    s.len() == k && all_positive(s) && is_strictly_increasing(s) && sum_seq(s) == n
}

spec fn is_possible(n: int, k: int) -> bool
{
    k * (k + 1) / 2 <= n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix find_smallest_sequence recursion and proof */
fn find_smallest_sequence(n: int, start: int, remaining: int) -> (s: Seq<int>)
    requires
        n > 0, start > 0, remaining > 0,
        remaining * (2 * start + remaining - 1) / 2 <= n
    ensures
        s.len() == remaining, is_strictly_increasing(s), all_positive(s), sum_seq(s) == n,
        forall|i: int| 0 <= i < s.len() ==> s[i] >= start
    decreases remaining
{
    if remaining == 1 {
        seq![n]
    } else {
        let next_start = start + 1;
        let remaining_min_sum = next_start * (remaining - 1);
        let max_val = n - remaining_min_sum;
        proof {
            assert(max_val >= start) by {
                let total_min = remaining * (2 * start + remaining - 1) / 2;
                assert(total_min <= n);
                assert(remaining_min_sum == next_start * (remaining - 1));
                assert(max_val == n - remaining_min_sum);
                // Calculate: total_min - remaining_min_sum
                let diff = total_min - remaining_min_sum;
                calc! {
                    diff;
                    == { }
                    remaining * (2 * start + remaining - 1) / 2 - next_start * (remaining - 1);
                    == { }
                    start;
                }
                assert(diff <= max_val);
            }
        }
        let first = start;
        let rest = find_smallest_sequence(n - first, next_start, remaining - 1);
        seq![first].add(rest)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: Vec<i8>)
    requires 
        valid_input(n as int, k as int)
    ensures 
        ((result.len() == 1 && result[0] == -1) || 
         (valid_sequence(result@.map(|_i: int, x: i8| x as int), n as int, k as int))) &&
        ((result.len() == 1 && result[0] == -1) <==> !is_possible(n as int, k as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix ghost block syntax */
{
    let n_int = n as int;
    let k_int = k as int;
    
    if !is_possible(n_int, k_int) {
        vec![-1]
    } else {
        proof {
            let smallest_seq_ghost = find_smallest_sequence(n_int, 1, k_int);
            assert(valid_sequence(smallest_seq_ghost, n_int, k_int));
        }
        let smallest_seq_ghost = find_smallest_sequence(n_int, 1, k_int);
        let mut result = Vec::with_capacity(k as usize);
        let mut i: usize = 0;
        while i < k_int as usize
            invariant
                i <= smallest_seq_ghost.len(),
                result.len() == i,
                forall|j: int| 0 <= j < i ==> result@[j] == smallest_seq_ghost[j] as i8
        {
            result.push(smallest_seq_ghost[i] as i8);
            i += 1;
        }
        result
    }
}
// </vc-code>


}

fn main() {}