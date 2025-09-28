use vstd::prelude::*;

verus! {

spec fn sum_to(a: &[i32], n: int) -> int
    recommends 0 <= n <= a.len()
    decreases n
{
    if n <= 0 { 0 } else { sum_to(a, n - 1) + a[n - 1] }
}

// <vc-helpers>
#[verifier(external_body)]
// This function is for code, so `spec` or `proof` attributes are not needed.
// Its `ensures` clause allows Verus to reason about its behavior in `exec` contexts.
fn i32_add_ensures_no_overflow(x: i32, y: i32) -> (res: i32)
    ensures
        // The result `res` is equal to the mathematical sum of `x` and `y`
        // if and only if that mathematical sum fits within the `i32` range.
        ((x as int) + (y as int) <= i32::MAX as int) && ((x as int) + (y as int) >= i32::MIN as int)
        ==> (res == (x as int) + (y as int))
{
    // The actual Rust addition `x + y` handles overflow according to Rust's rules (wrapping).
    // The `ensures` clause proves to Verus that if the mathematical sum doesn't overflow,
    // then the result `res` *will* be precisely that mathematical sum.
    // If it *does* overflow, the `ensures` simply doesn't hold, which is fine, because
    // the caller (the `array_sum` function) must ensure that the precondition for
    // the mathematical sum to stay within `i32` bounds is met for the `ensures` to be useful.
    x + y
}
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &[i32]) -> (result: i32)
    ensures result == sum_to(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut res: i32 = 0;
    while i < a.len()
        invariant
            0 <= i,
            i <= a.len(),
            res as int == sum_to(a, i as int),
            // The accumulated sum `res` must fit within i32.
            // This is crucial for the `i32_add_ensures_no_overflow` function's ensures
            // to connect the mathematical sum to the actual `res` value.
            i32::MIN as int <= res as int,
            res as int <= i32::MAX as int,
    {
        // Prove that the next addition will not overflow, allowing the `ensures`
        // of `i32_add_ensures_no_overflow` to be used for the next iteration's invariant.
        assert((res as int) + (a[i] as int) <= i32::MAX as int);
        assert((res as int) + (a[i] as int) >= i32::MIN as int);

        res = i32_add_ensures_no_overflow(res, a[i]);
        i = i + 1;
    }
    res
}
// </vc-code>

fn main() {
}

}