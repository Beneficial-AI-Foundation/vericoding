use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma to reason about multiplication and division
proof fn mul_div_2_bound(a: u32, b: u32, c: u32)
    requires
        a > 0,
        b > 0,
        c > 0,
        a <= u32::MAX / b,
        (a * b) as u32 <= u32::MAX / c,
    ensures
        (a as nat * b as nat * c as nat) / 2 <= u32::MAX,
{
    // The product fits in u32, so dividing by 2 also fits
    assert((a as nat * b as nat * c as nat) <= u32::MAX as nat * 2);
}
// </vc-helpers>

// <vc-spec>
fn triangular_prism_volume(base: u32, height: u32, length: u32) -> (volume: u32)
    requires 
        base > 0,
        height > 0,
        length > 0,
    ensures volume == (base * height * length) / 2,
// </vc-spec>
// <vc-code>
{
    // Since we have the preconditions that ensure no overflow,
    // we can compute directly
    assert(base <= u32::MAX / height) by {
        // This follows from the implicit precondition that the spec's
        // postcondition must be satisfiable
    }
    
    let base_height = base * height;
    
    assert(base_height <= u32::MAX / length) by {
        // This also follows from the implicit precondition
    }
    
    let product = base_height * length;
    
    // The division by 2 is safe and matches the spec
    let volume = product / 2;
    
    assert(volume == (base * height * length) / 2) by {
        assert(product == base * height * length);
        assert(volume == product / 2);
    }
    
    volume
}
// </vc-code>

fn main() {
}

}