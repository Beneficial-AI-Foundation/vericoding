// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn sum_abs(arr: Seq<int>, i: int) -> int
    recommends 0 <= i <= arr.len()
    decreases arr.len() - i
{
    if i == arr.len() { 0 }
    else { (if arr[i] >= 0 { arr[i] } else { -arr[i] }) + sum_abs(arr, i + 1) }
}

spec fn valid_input(n: int, arr: Seq<int>) -> bool
{
    0 <= n == arr.len()
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, arr: Seq<int>) -> (result: int)
    requires valid_input(n, arr)
    ensures result == sum_abs(arr, 0)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}