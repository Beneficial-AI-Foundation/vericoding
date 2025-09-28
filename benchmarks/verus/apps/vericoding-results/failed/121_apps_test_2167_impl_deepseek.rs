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
/* helper modified by LLM (iteration 5): Fixed sum_seq to work with i8 values */
spec fn sum_seq_i8(s: Seq<i8>) -> i32
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] as i32 + sum_seq_i8(s.subrange(1, s.len() as int))
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, arr: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, arr@.map(|i: int, x: i8| x as int))
    ensures correct_result(n as int, arr@.map(|i: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type compatibility with i8 sequences */
    let mut total: i32 = 0;
    let mut idx: usize = 0;
    
    while idx < arr.len()
        invariant
            total == sum_seq_i8(arr@.subrange(0, idx as int)),
            idx <= arr.len(),
        decreases arr.len() - idx
    {
        total = total + arr[idx] as i32;
        idx = idx + 1;
    }
    
    let n_int: i32 = n as i32;
    if total % n_int == 0 {
        n
    } else {
        n - 1
    }
}
// </vc-code>


}

fn main() {}