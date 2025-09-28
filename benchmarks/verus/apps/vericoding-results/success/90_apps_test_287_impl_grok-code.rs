// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int) -> bool
{
    n >= 1 && k >= 0 && k <= n
}

spec fn valid_output(result: Seq<int>, n: int, k: int) -> bool
{
    result.len() == 2 && 
    result[0] >= 0 && 
    result[1] >= 0 && 
    result[0] <= result[1] &&
    result[0] <= n - k &&
    result[1] <= n - k
}

spec fn min_good_apartments(n: int, k: int) -> int
{
    if k == 0 || k == n { 0 } else { 1 }
}

spec fn max_good_apartments(n: int, k: int) -> int
{
    if k == 0 || k == n { 0 }
    else if n - k < k * 2 { n - k }
    else { k * 2 }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: Vec<i8>)
    requires valid_input(n as int, k as int)
    ensures 
        result.len() == 2 &&
        valid_output(result@.map(|i: int, x: i8| x as int), n as int, k as int) &&
        result[0] as int == min_good_apartments(n as int, k as int) &&
        result[1] as int == max_good_apartments(n as int, k as int)
// </vc-spec>
// <vc-code>
{
    let min_val: i8 =
        if k == 0 || k == n {
            0
        } else {
            1
        };

    let nk_val: i32 = n as i32 - k as i32;
    let k2_val: i32 = k as i32 * 2;
    let max_val_i32: i32 =
        if nk_val < k2_val {
            nk_val
        } else {
            k2_val
        };
    let max_val: i8 = max_val_i32 as i8;

    let mut result = Vec::with_capacity(2);
    result.push(min_val);
    result.push(max_val);
    result
}
// </vc-code>


}

fn main() {}