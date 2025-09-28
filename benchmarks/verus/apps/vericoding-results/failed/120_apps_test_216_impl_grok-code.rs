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
/* helper modified by LLM (iteration 4): modified sum_abs_up_to to take Seq<i8> instead of Seq<int> to avoid lambda expression in invariants */
spec fn sum_abs_up_to(arr: Seq<i8>, start: int, end: int) -> int
    decreases end - start when 0 <= start <= end <= arr.len()
{
    if start == end {
        0
    } else {
        let v = arr[start] as int;
        (if v >= 0 { v } else { -v }) + sum_abs_up_to(arr, start + 1, end)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, arr: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, arr@.map(|i: int, v: i8| v as int))
    ensures result as int == sum_abs(arr@.map(|i: int, v: i8| v as int), 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): updated invariant to use arr@ directly without map lambda */
    let mut sum_i32: i32 = 0;
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            sum_i32 == sum_abs_up_to(arr@, 0, i as int),
            i8::MIN as i32 <= sum_i32 <= i8::MAX as i32,
        decreases arr.len() - i
    {
        let delta_int = if arr[i] >= 0 { arr[i] as i32 } else { -(arr[i] as i32) };
        assert(i8::MIN as i32 <= sum_i32 + delta_int);
        assert(sum_i32 + delta_int <= i8::MAX as i32);
        sum_i32 += delta_int;
        i += 1;
    }
    sum_i32 as i8
}
// </vc-code>


}

fn main() {}