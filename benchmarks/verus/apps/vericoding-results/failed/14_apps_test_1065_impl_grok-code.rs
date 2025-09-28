// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int, m: int, d: int) -> bool {
    2 <= n && 2 <= k <= n && 1 <= m <= n && 1 <= d <= n && m * d * k >= n
}

spec fn candies_used(x: int, d: int, k: int) -> int {
    x * ((d - 1) * k + 1)
}

spec fn valid_distribution(x: int, d: int, n: int, k: int, m: int, d_max: int) -> bool {
    1 <= x <= m && 1 <= d <= d_max && candies_used(x, d, k) <= n
}

spec fn person1_candies(x: int, d: int) -> int {
    x * d
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, m: i8, d: i8) -> (result: i8)
    requires valid_input(n as int, k as int, m as int, d as int)
    ensures
        result >= 0 &&
        result as int <= m as int * d as int &&
        (forall|x: int, d_val: int| valid_distribution(x, d_val, n as int, k as int, m as int, d as int) ==> person1_candies(x, d_val) <= result as int) &&
        (exists|x: int, d_val: int| valid_distribution(x, d_val, n as int, k as int, m as int, d as int) && person1_candies(x, d_val) == result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Changed to use i32 for executable integer types to avoid compilation errors with 'int' in exec code. */
{
    let nn: i32 = n as i32;
    let kk: i32 = k as i32;
    let mm: i32 = m as i32;
    let dd_max: i32 = d as i32;
    let mut max_candies: i32 = 0;
    let mut x: i32 = 1;
    while x <= mm
        invariant
            1 <= x,
            x <= mm + 1,
            0 <= max_candies,
            max_candies <= mm * dd_max,
            forall |x_prev: int, d_val_prev: int| 
                (if #x as int > x_prev as int) || (x as int == x_prev && #d_val as int < d_val_prev and d_val_prev <= dd_max)
                ==> valid_distribution(x_prev as int, d_val_prev as int, nn as int, kk as int, mm as int, dd_max as int)
                && person1_candies(x_prev as int, d_val_prev as int) <= max_candies as int,
        decreases mm - x + 1
    {
        let mut d_val: i32 = 1;
        while d_val <= dd_max
            invariant
                1 <= d_val,
                d_val <= dd_max + 1,
                1 <= x,
                x <= mm,
                0 <= max_candies,
                max_candies <= mm * dd_max,
                forall |d_val_prev: int| (d_val_prev < d_val as int)
                ==> valid_distribution(x as int, d_val_prev, nn as int, kk as int, mm as int, dd_max as int)
                ==> person1_candies(x as int, d_val_prev) <= max_candies as int,
            decreases dd_max - d_val + 1
        {
            if valid_distribution(x as int, d_val as int, nn as int, kk as int, mm as int, dd_max as int) {
                let candies = person1_candies(x as int, d_val as int);
                if candies > max_candies as int {
                    max_candies = candies as i32;
                }
            }
            d_val = d_val + 1;
        }
        x = x + 1;
    }
    max_candies as u32
}
// </vc-code>


}

fn main() {}