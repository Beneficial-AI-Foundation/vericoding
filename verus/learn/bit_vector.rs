use vstd::prelude::*;

verus! {
    fn main() {
    }

    fn test_passes(b: u32) {
//        println!("Testing bit vector with b = {}", b);
        assert(b & 1 == b % 2) by (bit_vector);
        assert(b & 7 == b % 8) by (bit_vector);
        assert(b & 0xff < 0x100) by (bit_vector);
    }

    fn test_success(x: u32, y: u32)
    requires
        x == y,
    {
        assert(x & 3 == y & 3) by (bit_vector)
            requires
             x == y,
        ;  // now x == y is available for the bit_vector proof
    }
    
    proof fn de_morgan_auto() by (bit_vector)
    ensures
        forall|a: u32, b: u32| #[trigger] (!(a & b)) == !a | !b,
        forall|a: u32, b: u32| #[trigger] (!(a | b)) == !a & !b,
    {

    }

    proof fn test_overflow_check(a: u8, b: u8) {
        // `a` and `b` are both `u8` integers, but we can test if their addition
        // overflows a `u8` by simply writing `a + b < 256`.
        assert((a & b) == 0 ==> (a | b) == (a + b) && (a + b) < 256) by(bit_vector);
    }

    proof fn test_truncation(a: u64) {
        assert(a as u32 == a & 0xffff_ffff) by(bit_vector);

        // You can write an identity with modulus as well:
        assert(a as u32 == a % 0x1_0000_0000) by(bit_vector);
    }

    proof fn test_truncating_add(a: u64, b: u64) {
        assert(add(a, b) == (a + b) as u64) by(bit_vector);
    }

    proof fn test_xor_u32_vs_u64(x: u32, y: u32) {
       assert((x as u64) ^ (y as u64) == (x ^ y) as u64) by(bit_vector);

        // XOR operation is independent of bitwidth so we don't even
        // need the `bit_vector` solver to do this:
        assert((x as u64) ^ (y as u64) == (x ^ y) as u64);
    }
}
