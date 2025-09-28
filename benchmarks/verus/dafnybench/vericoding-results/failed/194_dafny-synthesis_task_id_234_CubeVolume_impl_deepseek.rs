use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn cube_lemma(n: nat)
    requires
        n <= 46340, // To avoid integer overflow in i32 calculations
    ensures
        (n as int) * (n as int) * (n as int) == (n * n * n) as int,
{
    assert((n as int) * (n as int) == (n * n) as int);
    assert((n as int) * (n as int) * (n as int) == ((n * n) as int) * (n as int));
    assert(((n * n) as int) * (n as int) == ((n * n) * n) as int);
}

spec fn mul_assoc_property() -> bool {
    forall|x: int, y: int, z: int| #[trigger] (x * y * z) == x * (y * z)
}

proof fn mul_associative()
    ensures
        mul_assoc_property(),
{
    assert forall|x: int, y: int, z: int| #[trigger] (x * y * z) == x * (y * z) by {
        assert(x * y * z == x * (y * z));
    }
}

proof fn nat_into_int_mul_commutes(m: nat, n: nat)
    ensures
        (m as int) * (n as int) == (m * n) as int,
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn cube_volume(size: i32) -> (volume: i32)
    requires size > 0
    ensures volume == size * size * size
// </vc-spec>
// <vc-code>
{
    proof {
        mul_associative();
        cube_lemma(size as nat);
    }
    assert(size <= 1290) by {
        // 1290 is cube root of i32::MAX (approximately 1290.159...)
        // This ensures size * size * size doesn't overflow i32
        assert(size * size <= 1664100); // 1290 * 1290 = 1,664,100
        assert(size * size * size <= 2146689000); // 1290^3 = 2,146,689,000 < i32::MAX(2,147,483,647)
    };
    let volume = size * size * size;
    assert(volume == size * (size * size)) by {
        assert(mul_assoc_property());
    };
    volume
}
// </vc-code>

fn main() {
}

}