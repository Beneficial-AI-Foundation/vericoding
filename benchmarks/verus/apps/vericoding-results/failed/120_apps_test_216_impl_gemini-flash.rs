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
/* helper modified by LLM (iteration 5): Removed unused helper from previous iteration. */
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, arr: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, arr@.map(|i: int, v: i8| v as int))
    ensures result as int == sum_abs(arr@.map(|i: int, v: i8| v as int), 0)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type conversions to only use `as int` for `i8` to `int` when directly relating to ghost code or `Seq<int>` elements. Changed `n_int` to `n_usize` and `i` to `usize` for concrete iteration to resolve compilation errors. */
{
    let n_usize: usize = n as usize;
    let arr_int: Seq<int> = arr@.map(|_i: int, v: i8| v as int);
    let mut i: usize = 0;
    let mut current_sum: i8 = 0;

    while i < n_usize
        invariant
             0 <= i as int <= n as int,
             current_sum as int == sum_abs(arr_int, 0) - sum_abs(arr_int, i as int),
             arr_int.len() == n as int,
        decreases n_usize - i
    {
        let val = arr@[i];
        let abs_val = if val >= 0 { val } else { -val };
        current_sum = current_sum + abs_val;
        i = i + 1;
    }
    
    current_sum
}
// </vc-code>


}

fn main() {}