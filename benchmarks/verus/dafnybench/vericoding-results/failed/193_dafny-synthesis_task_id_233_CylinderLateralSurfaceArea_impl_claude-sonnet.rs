use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_mul_bounds(a: u64, b: u64, c: u64)
    requires 
        a <= u64::MAX / b,
        (a as int) * (b as int) <= (u64::MAX as int) / (c as int),
    ensures 
        a.checked_mul(b).is_some(),
        ((a as int) * (b as int) * (c as int)) <= u64::MAX,
{
}

proof fn lemma_computation_valid(radius: u64, height: u64)
    requires 
        radius > 0,
        height > 0,
        radius <= u64::MAX / 2,
        (2 * radius) <= u64::MAX / height,
        ((2 * radius) as int) * (height as int) <= (u64::MAX as int) / 314,
    ensures 
        (2u64 * radius).checked_mul(height).is_some(),
        (((2u64 * radius) as int) * (height as int) * 314) <= u64::MAX,
{
    lemma_mul_bounds(2u64 * radius, height, 314);
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
    assert(radius <= u64::MAX / 2) by {
        assert(u64::MAX >= 18446744073709551615);
        assert(radius <= 9223372036854775807);
    }
    
    assert((2 * radius) <= u64::MAX / height) by {
        assert((2 * radius) as int * height as int <= u64::MAX);
    }
    
    assert(((2 * radius) as int) * (height as int) <= (u64::MAX as int) / 314) by {
        assert(((2 * radius) as int) * (height as int) * 314 <= u64::MAX);
    }
    
    proof {
        lemma_computation_valid(radius, height);
    }
    
    let intermediate1 = (2u64 * radius).checked_mul(height).unwrap();
    let intermediate2 = intermediate1.checked_mul(314).unwrap();
    let result = intermediate2 / 100;
    
    proof {
        assert(intermediate1 == 2 * radius * height);
        assert(intermediate2 == 2 * radius * height * 314);
        assert(result == 2 * radius * height * 314 / 100);
    }
    
    result
}
// </vc-code>

fn main() {
}

}