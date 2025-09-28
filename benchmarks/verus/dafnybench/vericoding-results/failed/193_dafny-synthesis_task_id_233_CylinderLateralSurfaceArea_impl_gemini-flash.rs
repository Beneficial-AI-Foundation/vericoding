use vstd::prelude::*;

verus! {

// <vc-helpers>
const PI_APPROX_NUMERATOR: u64 = 314;
const PI_APPROX_DENOMINATOR: u64 = 100;

proof fn mul_associativity(x: int, y: int, z: int)
    ensures (x * y) * z == x * (y * z)
{
    // This is a basic property of integer multiplication
    // The assertion is not needed as Verus already knows this.
}

proof fn mul_commutative(x: int, y: int)
    ensures x * y == y * x
{
    // Basic property of integer multiplication
    // The assertion is not needed as Verus already knows this.
}
// </vc-helpers>

// <vc-spec>
fn cylinder_lateral_surface_area(radius: u64, height: u64) -> (area: u64)
    requires 
        radius > 0,
        height > 0,
    ensures area == 2 * radius * height * 314 / 100,
// </vc-spec>
// <vc-code>
{
    // Lateral surface area of a cylinder = 2 * pi * radius * height
    // Using pi_approx = 314/100

    let mut result_numerator: u64 = 0;

    // Calculate 2 * radius
    let two_r: u64 = 2u64.checked_mul(radius).expect("2 * radius overflows u64");
    assert(two_r == 2 * radius) by (nonlinear_arith);

    // Calculate (2 * radius) * height
    let two_r_h: u64 = two_r.checked_mul(height).expect("(2 * radius) * height overflows u64");
    assert(two_r_h == 2 * radius * height) by (nonlinear_arith);

    // Calculate (2 * radius * height) * pi_approx_numerator
    let product_with_pi_num: u64 = two_r_h.checked_mul(PI_APPROX_NUMERATOR).expect("(2 * radius * height) * PI_APPROX_NUMERATOR overflows u64");
    assert(product_with_pi_num == 2 * radius * height * 314) by (nonlinear_arith);


    // The final result is (product_with_pi_num / PI_APPROX_DENOMINATOR)
    result_numerator = product_with_pi_num / PI_APPROX_DENOMINATOR;


    assert(result_numerator == (2 * radius * height * 314) / 100) by (nonlinear_arith);


    result_numerator
}
// </vc-code>

fn main() {
}

}