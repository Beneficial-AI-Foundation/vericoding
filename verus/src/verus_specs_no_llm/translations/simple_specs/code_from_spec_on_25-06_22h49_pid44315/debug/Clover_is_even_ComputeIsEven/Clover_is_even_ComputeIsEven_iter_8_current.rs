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
    assert(x == (x - 2) + 2);
    assert(x % 2 == ((x - 2) + 2) % 2);
    assert(((x - 2) + 2) % 2 == ((x - 2) % 2 + 2 % 2) % 2) by(nonlinear_arith);
    assert(2 % 2 == 0);
    assert(((x - 2) % 2 + 2 % 2) % 2 == ((x - 2) % 2 + 0) % 2);
    assert(((x - 2) % 2 + 0) % 2 == (x - 2) % 2) by(nonlinear_arith);
}

// Helper lemma for adding 2 preserves evenness/oddness
proof fn lemma_mod_add_2(x: int)
    ensures (x % 2 == 0) == ((x + 2) % 2 == 0)
{
    assert(x + 2 == x + 2);
    assert((x + 2) % 2 == (x % 2 + 2 % 2) % 2) by(nonlinear_arith);
    assert(2 % 2 == 0);
    assert((x % 2 + 2 % 2) % 2 == (x % 2 + 0) % 2);
    assert((x % 2 + 0) % 2 == x % 2) by(nonlinear_arith);
}

fn ComputeIsEven(x: int) -> (is_even: bool)
    ensures
        (x % 2 == 0) == is_even
    decreases x.abs()
{
    if x >= 0 {
        if x == 0 {
            assert(0 % 2 == 0);
            true
        } else if x == 1 {
            assert(1 % 2 == 1);
            assert(1 % 2 != 0);
            false
        } else {
            assert(x >= 2);
            assert((x - 2).abs() < x.abs());
            proof {
                lemma_mod_sub_2(x);
            }
            let result = ComputeIsEven(x - 2);
            assert(((x - 2) % 2 == 0) == result);
            assert((x % 2 == 0) == ((x - 2) % 2 == 0));
            assert((x % 2 == 0) == result);
            result
        }
    } else {
        // x < 0
        if x == -1 {
            assert(-1 % 2 == -1);  // In Rust/Verus, -1 % 2 = -1
            assert(-1 % 2 != 0);
            false
        } else {
            // x <= -2, so x + 2 <= 0 and |x + 2| < |x|
            assert(x <= -2);
            assert((x + 2).abs() < x.abs());
            proof {
                lemma_mod_add_2(x);
            }
            let result = ComputeIsEven(x + 2);
            assert(((x + 2) % 2 == 0) == result);
            assert((x % 2 == 0) == ((x + 2) % 2 == 0));
            assert((x % 2 == 0) == result);
            result
        }
    }
}

}