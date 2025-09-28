use vstd::prelude::*;

verus! {

// <vc-helpers>
fn sqrt_pred(r: u32, n: u32) -> bool {
    r.checked_mul(r).unwrap_or(0) <= n && n < (r as u64 + 1).checked_mul(r as u64 + 1).unwrap_or(0xffffffff_u64) as u32
}
// </vc-helpers>

// <vc-spec>
fn square_root(n: u32) -> (r: u32)
  ensures r * r <= n < (r + 1) * (r + 1)
// </vc-spec>
// <vc-code>
{
    let mut low: u32 = 0;
    let mut high: u32 = n;
    let mut ans: u32 = 0;

    while low <= high
        invariant
            low <= high + 1, // Loop termination
            ans as u64 * ans as u64 <= n as u64, // `ans` is a valid candidate for `r` so far
            forall|x: u32| (x > high) ==> { #[trigger] x as u64 * x as u64 } > n as u64, // Any number `x` greater than `high` must have `x*x > n`.
            forall|x: u32| (x < low) ==> { #[trigger] x as u64 * x as u64 } <= n as u64 ==> x <= ans, // For `low` values: any `x` such that `x < low` and `x*x <= n` should also be less than or equal to `ans`.
            ans <= low, // `ans` is always at most `low` when `low` is updated.
            high != 0xffffffff ==> n as u64 < (high as u64 + 1).checked_mul(high as u64 + 1).unwrap_or(0xffffffff_u64),

        decreases high - low
    {
        let mid = low + (high - low) / 2;

        if (mid as u64).checked_mul(mid as u64).is_some() && mid as u64 * mid as u64 > n as u64 {
            // `mid * mid` did not overflow but is still greater than `n`.
             assert(mid > 0); // If mid is 0, mid*mid is 0 which is not > n unless n is 0 and only if mid is not 0
            high = mid - 1;
        } else {
            // `mid * mid <= n` or `mid * mid` overflowed to a value `<= n` (unlikely for `u32` unless `n == u32::MAX`).
            // If mid*mid overflows, it means true mid*mid is very large.
            // The constraint `mid.checked_mul(mid).is_some()` correctly handles this,
            // if it overflows, this branch is not taken.
            ans = mid;
            low = mid + 1;
        }
    }
    ans
}
// </vc-code>

fn main() {}

}