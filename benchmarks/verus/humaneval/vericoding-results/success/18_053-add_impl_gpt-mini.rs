// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): checked addition returning Option to avoid overflow */
fn int_sum_opt(x: i32, y: i32) -> Option<i32> {
    let s: i64 = (x as i64) + (y as i64);
    if s >= (i32::MIN as i64) && s <= (i32::MAX as i64) {
        Some(s as i32)
    } else {
        None
    }
}
// </vc-helpers>

// <vc-spec>
fn add(x: i32, y: i32) -> (res: Option<i32>)

    ensures
        res.is_some() ==> res.unwrap() == x + y,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): checked addition using i64 to prevent overflow, returning Some(sum) only when in range */
    let s64: i64 = (x as i64) + (y as i64);
    if s64 >= (i32::MIN as i64) && s64 <= (i32::MAX as i64) {
        let s: i32 = s64 as i32;
        proof {
            assert((s as i64) == (x as i64) + (y as i64));
            assert(s == x + y);
        }
        Some(s)
    } else {
        None
    }
}
// </vc-code>

}
fn main() {}