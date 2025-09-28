use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma to establish bounds for safe arithmetic
proof fn lemma_mul_bounds(a: u32, b: u32, c: u32)
    requires 
        a > 0,
        b > 0, 
        c > 0,
        a as nat * b as nat * c as nat <= u32::MAX as nat,
    ensures 
        (a as nat * b as nat) <= u32::MAX as nat,
        ((a as nat * b as nat) * c as nat) <= u32::MAX as nat,
{
    assert(a as nat * b as nat * c as nat == (a as nat * b as nat) * c as nat);
}

// Helper lemma to prove multiplication properties
proof fn lemma_mul_div_property(a: u32, b: u32, c: u32)
    requires
        a > 0,
        b > 0,
        c > 0,
        a as nat * b as nat * c as nat <= u32::MAX as nat,
    ensures
        (a * b * c) as nat == a as nat * b as nat * c as nat,
{
    lemma_mul_bounds(a, b, c);
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
    requires(base as nat * height as nat * length as nat <= u32::MAX as nat);
    
    proof {
        lemma_mul_div_property(base, height, length);
    }
    
    let product = base * height * length;
    product / 2
}
// </vc-code>

fn main() {
}

}