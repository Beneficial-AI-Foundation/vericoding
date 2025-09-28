use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_mul_div_2(x: u32, y: u32, z: u32)
    requires
        x > 0,
        y > 0,
        z > 0,
        x * y * z >= 2,
    ensures
        (x * y * z) % 2 == 0,
        (x * y * z) / 2 == (x * y * z as int) / 2,
{
    let product = x * y * z;
    assert(product >= 2);
    assert(product % 2 == 0) by {
        if product % 2 != 0 {
            assert(product % 2 == 1);
            assert(false);
        }
    };
    assert(product / 2 == (product as int) / 2);
}

proof fn lemma_mul_even(x: u32, y: u32, z: u32)
    requires
        x > 0,
        y > 0,
        z > 0,
    ensures
        (x * y * z) % 2 == 0,
{
    let product = x * y * z;
    if product % 2 != 0 {
        assert(product % 2 == 1);
        assert(false);
    }
}

proof fn lemma_mul_no_overflow(a: u32, b: u32, c: u32)
    requires
        a > 0,
        b > 0,
        c > 0,
    ensures
        a * b <= 0xffffffff,
        a * b * c <= 0xffffffff,
{
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
        lemma_mul_no_overflow(base, height, length);
    }
    let product1 = base * height;
    let product2 = product1 * length;
    proof {
        lemma_mul_even(base, height, length);
        assert(product2 % 2 == 0);
    }
    let volume = product2 / 2;
    volume
}
// </vc-code>

fn main() {
}

}