use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn mul_commutes(a: u64, b: u64, c: u64)
    ensures
        a * b * c == a * c * b,
{
    assert(a * b * c == a * (b * c)) by (nonlinear_arith);
    assert(a * c * b == a * (c * b)) by (nonlinear_arith);
    assert(b * c == c * b) by (nonlinear_arith);
}

proof fn mul_associates(a: u64, b: u64, c: u64)
    ensures
        a * b * c == (a * b) * c,
{
}

proof fn div_mul_combine(a: u64, b: u64, c: u64)
    requires
        c > 0,
    ensures
        (a as int) * (b as int) / (c as int) == ((a * b) as int) / (c as int),
{
}

proof fn calculation_lemma(radius: u64, height: u64)
    ensures
        (2 * radius * height * 314) / 100 == 2 * radius * height * 314 / 100,
{
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
    proof {
        mul_associates(2, radius, height);
        mul_commutes((2u64 * radius) as u64, height, 314);
        mul_associates((2u64 * radius) as u64, 314, height);
        div_mul_combine(((2u64 * radius) * 314) as u64, height, 100);
        calculation_lemma(radius, height);
    }
    
    let area: u64 = 2u64 * radius * height * 314u64 / 100u64;
    area
}
// </vc-code>

fn main() {
}

}