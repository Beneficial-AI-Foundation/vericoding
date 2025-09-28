use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn triple_u32_prod_lt_1_shl_96(b: u32, h: u32, l: u32)
{
    let bb: u128 = b as u128;
    let hh: u128 = h as u128;
    let ll: u128 = l as u128;
    // each u32 value is strictly less than 2^32 when viewed as u128
    assert(bb < (1u128 << 32));
    assert(hh < (1u128 << 32));
    assert(ll < (1u128 << 32));
    // multiply bounds: bb*hh < 2^64, and bb*hh*ll < 2^96
    assert(bb * hh < (1u128 << 64));
    assert(bb * hh * ll < (1u128 << 96));
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
    proof {
        triple_u32_prod_lt_1_shl_96(base, height, length);
    }
    let prod: u128 = (base as u128) * (height as u128) * (length as u128);
    let vol128: u128 = prod / 2u128;
    #[verifier::truncate] (vol128 as u32)
}
// </vc-code>

fn main() {
}

}