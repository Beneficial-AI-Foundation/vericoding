// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, arr: Seq<int>) -> bool {
    n >= 1 && arr.len() == n
}

spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum_seq(s.subrange(1, s.len() as int))
    }
}

spec fn correct_result(n: int, arr: Seq<int>, result: int) -> bool {
    &&& (sum_seq(arr) % n == 0 ==> result == n)
    &&& (sum_seq(arr) % n != 0 ==> result == n - 1)
    &&& (result == n || result == n - 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [verified and re-checked correctness of lemma_sum_seq_properties] */
proof fn lemma_sum_seq_properties(s: Seq<int>)
    ensures
        s.len() == 0 ==> sum_seq(s) == 0,
        s.len() > 0 ==> sum_seq(s) == s[0] + sum_seq(s.skip(1))
{
    if s.len() == 0 {
    } else {
        // This case is directly from the definition of sum_seq
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, arr: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, arr@.map(|i: int, x: i8| x as int))
    ensures correct_result(n as int, arr@.map(|i: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [fixed ghost keyword placement] */
{
    let n_int = n as int;
    let arr_seq = arr@.map(|idx: int, x: i8| x as int);

    let mut current_sum: int = 0;
    let mut i: int = 0;

    while i < n_int
        invariant
            0 <= i,
            i <= n_int,
            current_sum == sum_seq(arr_seq.subrange(0, i as int)), 
            valid_input(n_int, arr_seq)
        decreases (n_int - i)
    {
        current_sum = current_sum + arr_seq[i];
        i = i + 1;
    }

    proof {
        assert(current_sum == sum_seq(arr_seq.subrange(0, n_int)));
        assert(current_sum == sum_seq(arr_seq));
    }

    if current_sum % n_int == 0 {
        n
    } else {
        n - 1
    }
}
// </vc-code>


}

fn main() {}