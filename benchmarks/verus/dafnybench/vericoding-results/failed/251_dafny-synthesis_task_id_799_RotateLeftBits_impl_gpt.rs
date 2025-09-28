use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn bounds_for_32_minus_d(d: int)
    requires
        0 <= d < 32,
    ensures
        0 <= 32 - d <= 32
{
    assert(0 <= 32 - d) by {
        assert(32 >= d);
    }
    assert(32 - d <= 32);
}

proof fn bounds_for_32_minus_d_strict(d: int)
    requires
        0 < d < 32,
    ensures
        0 < 32 - d < 32
{
    assert(32 - d < 32) by {
        assert(d > 0);
    }
    assert(0 < 32 - d) by {
        assert(d < 32);
    }
}

proof fn shr_u32_by_32_is_zero(n: u32)
    ensures
        n >> 32 == 0u32
{
    assert(n >> 32 == 0u32);
}
// </vc-helpers>

// <vc-spec>
fn rotate_left_bits(n: u32, d: int) -> (result: u32)
    requires 0 <= d < 32
    ensures result == ((n << d) | (n >> (32 - d)))
// </vc-spec>
// <vc-code>
{
    if d == 0 {
        let left = n << d;
        let right: u32 = 0u32;
        proof {
            assert(32 - d == 32);
            shr_u32_by_32_is_zero(n);
            assert(right == n >> (32 - d));
        }
        let res = left | right;
        res
    } else {
        proof {
            assert(0 < d);
            bounds_for_32_minus_d_strict(d);
        }
        let res: u32 = (n << d) | (n >> (32 - d));
        res
    }
}
// </vc-code>

fn main() {
}

}