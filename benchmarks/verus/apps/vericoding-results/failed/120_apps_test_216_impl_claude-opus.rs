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

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, arr: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, arr@.map(|i: int, v: i8| v as int))
    ensures result as int == sum_abs(arr@.map(|i: int, v: i8| v as int), 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed invariant and added overflow prevention */
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    while i < n as usize
        invariant
            0 <= i <= n as int,
            i <= arr.len(),
            n as int == arr.len(),
            sum == sum_abs(arr@.map(|j: int, v: i8| v as int), 0) - sum_abs(arr@.map(|j: int, v: i8| v as int), i as int),
        decreases n as int - i as int
    {
        let val = arr[i] as i32;
        if val >= 0 {
            sum = sum + val;
        } else {
            sum = sum - val;
        }
        i = i + 1;
    }
    sum as i8
}
// </vc-code>


}

fn main() {}