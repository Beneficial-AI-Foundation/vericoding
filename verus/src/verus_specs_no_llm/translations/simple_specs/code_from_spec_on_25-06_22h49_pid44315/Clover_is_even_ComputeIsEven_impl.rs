use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper lemma for modular arithmetic
proof fn lemma_mod_sub_2(x: int)
    requires x >= 2
    ensures (x % 2 == 0) == ((x - 2) % 2 == 0)
{
    // Use the fundamental property of modular arithmetic
    assert(x == (x - 2) + 2);
    // For any integers a, b, c: (a + b) % c == (a % c + b % c) % c
    assert(x % 2 == ((x - 2) + 2) % 2);
    // Since 2 % 2 == 0, adding 2 doesn't change the remainder mod 2
    assert(2 % 2 == 0);
    // Use Verus's built-in understanding of modular arithmetic
    assert(((x - 2) + 2) % 2 == (x - 2) % 2);
}

// Helper lemma for adding 2 preserves evenness/oddness
proof fn lemma_mod_add_2(x: int)
    ensures (x % 2 == 0) == ((x + 2) % 2 == 0)
{
    // Adding 2 (which is divisible by 2) doesn't change the remainder mod 2
    assert(2 % 2 == 0);
    assert((x + 2) % 2 == x % 2);
}

fn ComputeIsEven(x: int) -> (is_even: bool)
    ensures
        (x % 2 == 0) == is_even
    decreases 
        if x >= 0 { x } else { -x }
{
    if x >= 0 {
        if x == 0 {
            // 0 is even
            assert(0 % 2 == 0);
            true
        } else if x == 1 {
            // 1 is odd
            assert(1 % 2 == 1);
            assert(1 % 2 != 0);
            false
        } else {
            // x >= 2
            assert(x >= 2);
            proof {
                lemma_mod_sub_2(x);
            }
            let result = ComputeIsEven(x - 2);
            // The lemma ensures that x and x-2 have the same parity
            assert((x % 2 == 0) == ((x - 2) % 2 == 0));
            // The recursive call ensures that result == ((x-2) % 2 == 0)
            assert(((x - 2) % 2 == 0) == result);
            // Therefore, (x % 2 == 0) == result
            result
        }
    } else {
        // x < 0
        if x == -1 {
            // In Rust/Verus, -1 % 2 == -1, which is not 0
            assert(-1 % 2 != 0);
            false
        } else if x == -2 {
            // -2 % 2 == 0
            assert(-2 % 2 == 0);
            true
        } else {
            // x <= -3, so x + 2 < 0 and |x + 2| < |x|
            assert(x <= -3);
            assert(x + 2 <= -1);
            assert(x + 2 < 0);
            assert(-x >= 3);
            assert(-(x + 2) >= 1);
            assert(-(x + 2) < -x);
            proof {
                lemma_mod_add_2(x);
            }
            let result = ComputeIsEven(x + 2);
            // The lemma ensures that x and x+2 have the same parity
            assert((x % 2 == 0) == ((x + 2) % 2 == 0));
            // The recursive call ensures that result == ((x+2) % 2 == 0)
            assert(((x + 2) % 2 == 0) == result);
            // Therefore, (x % 2 == 0) == result
            result
        }
    }
}

}