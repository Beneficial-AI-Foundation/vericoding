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
/* helper modified by LLM (iteration 5): convert Vec<i8> to Seq<int> */
spec fn seq_of_vec(arr: Vec<i8>) -> Seq<int>
{
    arr@.map(|i: int, x: i8| x as int)
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, arr: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, arr@.map(|i: int, x: i8| x as int))
    ensures correct_result(n as int, arr@.map(|i: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute sum with verified invariant and use runtime indexing */
    let mut i: usize = 0;
    let mut sum: i64 = 0;
    let n_usize: usize = n as usize;
    while i < n_usize
        invariant
            i <= n_usize,
            sum as int == sum_seq(seq_of_vec(arr).subrange(0, i as int)),
        decreases n_usize - i
    {
        let old_i = i;
        let old_sum = sum;
        let v: i8 = arr[i];
        sum = sum + (v as i64);
        i = i + 1;
        proof {
            assert(old_sum as int == sum_seq(seq_of_vec(arr).subrange(0, old_i as int)));
            assert(seq_of_vec(arr)@[old_i as int] == (v as int));
            assert(sum as int == old_sum as int + seq_of_vec(arr)@[old_i as int]);
            assert(sum as int == sum_seq(seq_of_vec(arr).subrange(0, i as int)));
        }
    }
    let res = if sum % (n as i64) == 0 {
        n
    } else {
        n - 1
    };
    res
}
// </vc-code>


}

fn main() {}