use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier(external_body)]
#[spec]
fn mul_spec(a: i32, b: i32) -> i32 {
    a * b
}
// </vc-helpers>

// <vc-spec>
fn cube_volume(size: i32) -> (volume: i32)
    requires size > 0
    ensures volume == size * size * size
// </vc-spec>
// <vc-code>
{
    let volume = size * size * size;
    proof {
        assert(size > 0);
        assert(size.checked_mul(size).is_some());
        assert(size.checked_mul(size).unwrap().checked_mul(size).is_some());
    }
    volume
}
// </vc-code>

fn main() {
}

}