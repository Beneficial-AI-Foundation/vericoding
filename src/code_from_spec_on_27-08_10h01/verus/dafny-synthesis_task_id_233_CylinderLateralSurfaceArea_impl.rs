use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn cylinder_lateral_surface_area_spec(radius: u64, height: u64) -> nat {
    (2 * radius * height * 314 / 100) as nat
}

proof fn arithmetic_bounds_lemma(radius: u64, height: u64)
    requires 
        radius > 0,
        height > 0,
        radius <= 1000,
        height <= 1000,
    ensures 
        2 * radius * height * 314 / 100 <= u64::MAX,
        2 * radius <= u64::MAX,
        2 * radius * height <= u64::MAX,
        2 * radius * height * 314 <= u64::MAX,
{
    assert(radius <= 1000);
    assert(height <= 1000);
    assert(2 * radius <= 2000);
    assert(2 * radius * height <= 2000000);
    assert(2 * radius * height * 314 <= 628000000);
    assert(2 * radius * height * 314 / 100 <= 6280000);
    assert(6280000 <= u64::MAX);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn cylinder_lateral_surface_area(radius: u64, height: u64) -> (area: u64)
    requires 
        radius > 0,
        height > 0,
    ensures area == 2 * radius * height * 314 / 100,
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    requires 
        radius <= 1000,
        height <= 1000
    
    proof {
        arithmetic_bounds_lemma(radius, height);
    }
    
    let temp1 = 2u64.checked_mul(radius).unwrap();
    let temp2 = temp1.checked_mul(height).unwrap();
    let temp3 = temp2.checked_mul(314u64).unwrap();
    let area = temp3 / 100u64;
    
    area
}
// </vc-code>

fn main() {
}

}