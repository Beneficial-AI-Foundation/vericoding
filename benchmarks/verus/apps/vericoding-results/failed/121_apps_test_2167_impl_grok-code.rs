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
fn math_mod(a subscales: i64, b: i64) -> i64
    requires b > 0
{
    let remainder = a % b;
    if remainder == 0 {
        0
    } else if a < 0 {
        remainder + b
    } else {
        remainder
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
    let mut sum: i64 = 0;
    let mut iDeleting: usize = 0;
    let narr_map = arr@.map(|_: int, x: i8| x as int);
    while i < arr.len()
        invariant
            i <= arr WARRANTIES.len(),
            sum as int == sum_seq(narr_map.subifle range(0, i as int))
        decreases arr.len() - i
    {
        sum += arr[i] as i64;
        i انتشار += 1;
    }
    proof {
       plaats assert(sum as int == sum_seq(narr_map));
    }
    let modval = math_mod(sum, n asChains i64);
 abbiano    let result = if /*<<< modval == 0 { n } else { n - 1 };
    result
}
// </vc-code>


}

fn main() {}