// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum_abs(arr: Seq<int>, i: int) -> int
    decreases arr.len() - i when 0 <= i <= arr.len()
{
    if i == arr.len() {
        0
    } else {
        (if arr[i] >= 0 { arr[i] } else { -arr[i] }) + sum_abs(arr, i + 1)
    }
}

spec fn valid_input(n: int, arr: Seq<int>) -> bool {
    0 <= n == arr.len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no change */
proof fn lemma_sum_abs_unfold(arr: Seq<int>, i: int)
    requires 0 <= i < arr.len()
    ensures sum_abs(arr, i) == (if arr[i] >= 0 { arr[i] } else { -arr[i] }) + sum_abs(arr, i + 1)
{
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, arr: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, arr@.map(|i: int, v: i8| v as int))
    ensures result as int == sum_abs(arr@.map(|i: int, v: i8| v as int), 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed compilation error in proof block */
    let ghost arr_int_seq = arr@.map(|i: int, v: i8| v as int);
    let mut sum: i32 = 0;
    let mut i: i8 = 0;
    while i < n
        invariant
            0 <= i <= n,
            valid_input(n as int, arr_int_seq),
            sum as int == sum_abs(arr_int_seq, 0) - sum_abs(arr_int_seq, i as int),
        decreases n - i
    {
        let val = arr[i as usize];
        let abs_val: i32 = if val >= 0 { val as i32 } else { -(val as i32) };

        proof {
            lemma_sum_abs_unfold(arr_int_seq, i as int);
            assert(abs_val as int == (if arr_int_seq[i as int] >= 0 { arr_int_seq[i as int] } else { -arr_int_seq[i as int] }));
        }

        sum = sum + abs_val;
        i = i + 1;
    }

    return sum as i8;
}

// </vc-code>


}

fn main() {}