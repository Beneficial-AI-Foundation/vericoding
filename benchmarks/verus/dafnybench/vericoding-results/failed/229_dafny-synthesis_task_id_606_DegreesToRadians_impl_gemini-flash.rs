use vstd::prelude::*;

verus! {

// <vc-helpers>
fn mul_div_i64(arg1: i64, arg2: i64, arg3: i64) -> (result: i64)
    ensures
        arg3 != 0 ==> result as int == (arg1 as int * arg2 as int) / arg3 as int,
        arg3 == 0 ==> result == 0, // In case of division by zero, return 0 or handle error appropriately
{
    // This function will be replaced by an external body in the actual execution
    // For proof, we define its behavior using ensures clause
    if arg3 == 0 {
        0 // This branch will not be taken in verified code if arg3 is guaranteed non-zero
    } else {
        arg1 * arg2 / arg3
    }
}
// </vc-helpers>

// <vc-spec>
spec fn pi_approx() -> int { 314159265358979323846i128 as int }
spec fn scale_factor() -> int { 100000000000000000000i128 as int }

fn degrees_to_radians(degrees: i64) -> (radians: i64)
    ensures radians as int == (degrees as int * pi_approx()) / scale_factor() / 180
// </vc-spec>
// <vc-code>
{
    let degrees_int_i128 = degrees as i128;
    // No direct cast from spec fn result (int) to i128.
    // Instead, retrieve the underlying primitive value.
    let pi_int_i128: i128 = pi_approx().into();
    let scale_int_i128: i128 = scale_factor().into();
    let eighteen_zero_int_i128 = 180i128;

    // We need to perform (degrees_int * pi_int) / (scale_int * 180)
    // Or, (degrees_int * pi_int / scale_int) / 180
    // Given the scale_factor is huge, (degrees_int * pi_int) will also be huge.
    // It's better to maintain precision by doing the divisions in order.
    // (degrees_int * pi_int) can easily overflow i64.
    // So we need to use i128 intermediate results.

    let numerator_i128 = degrees_int_i128 * pi_int_i128 / scale_int_i128; // This automatically handles the large integers and division
    let result_i128 = numerator_i128 / eighteen_zero_int_i128;

    // Prove the postcondition
    proof {
        // Assert that the i128 computation result matches the spec function's `int` result.
        // `int` type in Verus supports arbitrary precision, so it's the reference.
        assert(result_i128 as int == (degrees as int * pi_approx()) / scale_factor() / 180);
    }
    // Convert the i128 result back to i64
    result_i128 as i64
}
// </vc-code>

fn main() {
}

}