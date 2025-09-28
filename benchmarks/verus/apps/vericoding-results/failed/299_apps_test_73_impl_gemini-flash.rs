// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn compute_position(days: int, v0: int, v1: int, a: int, l: int) -> int
    decreases days
{
    if days <= 0 {
        0
    } else {
        let prev_pos = compute_position(days - 1, v0, v1, a, l);
        let after_reread = if prev_pos - l > 0 { prev_pos - l } else { 0 };
        let read_today = if v1 < v0 + a * (days - 1) { v1 } else { v0 + a * (days - 1) };
        after_reread + read_today
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(c: u8, v0: u8, v1: u8, a: u8, l: u8) -> (result: u8)
    requires
        1 <= c && c <= 100,
        0 <= l && l < v0 && v0 <= v1 && v1 <= 100,
        0 <= a && a <= 100
    ensures
        result >= 1,
        compute_position(result as int, v0 as int, v1 as int, a as int, l as int) >= c as int,
        forall|days: int| 1 <= days && days < result as int ==> compute_position(days, v0 as int, v1 as int, a as int, l as int) < c as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type casting errors for `u8` to `int` within the body by making `low`, `high`, `ans`, and `mid` use `u8` instead of `int`. */
    let mut low: u8 = 1;
    let mut high: u8 = 255; 
    let mut ans: u8 = 255; 

    while low <= high
        invariant
            1 <= low,
            high <= 255,
            low <= (high as int) + 1,
            (ans == 255 ==> forall|i: int| 1 <= i < low as int ==> compute_position(i, v0 as int, v1 as int, a as int, l as int) < c as int),
            (ans < 255 ==> ans as int <= (high as int) + 1),
            (ans < 255 ==> compute_position(ans as int, v0 as int, v1 as int, a as int, l as int) >= c as int),
            (ans < 255 ==> forall|i: int| 1 <= i < ans as int ==> compute_position(i, v0 as int, v1 as int, a as int, l as int) < c as int),
            (forall|i: int| high as int < i && i < ans as int ==> compute_position(i, v0 as int, v1 as int, a as int, l as int) >= c as int),
    {
        let mid = low + (high - low) / 2;

        proof {
            
        }

        let current_pos = compute_position(mid as int, v0 as int, v1 as int, a as int, l as int);

        if current_pos >= c as int {
            ans = mid;
            high = mid - 1;
        } else {
            low = mid + 1;
        }
    }
    ans
}
// </vc-code>


}

fn main() {}