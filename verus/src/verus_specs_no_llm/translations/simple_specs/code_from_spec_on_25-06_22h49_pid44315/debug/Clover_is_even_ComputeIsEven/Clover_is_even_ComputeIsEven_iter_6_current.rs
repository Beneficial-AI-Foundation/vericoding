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
    // The proof is automatic for this simple modular arithmetic property
}

// Helper lemma for negative numbers
proof fn lemma_mod_neg(x: int)
    ensures (x % 2 == 0) == ((-x) % 2 == 0)
{
    // The proof is automatic for this property
}

fn ComputeIsEven(x: int) -> (is_even: bool)
    ensures
        (x % 2 == 0) == is_even
    decreases x.abs()
{
    if x >= 0 {
        if x == 0 {
            true
        } else if x == 1 {
            false
        } else {
            assert(x >= 2);
            assert((x - 2).abs() < x.abs());
            proof {
                lemma_mod_sub_2(x);
            }
            ComputeIsEven(x - 2)
        }
    } else {
        // x < 0
        if x == -1 {
            false
        } else {
            // x <= -2, so x + 2 <= 0 and |x + 2| < |x|
            assert(x <= -2);
            assert((x + 2).abs() < x.abs());
            proof {
                lemma_mod_sub_2(-x);
                lemma_mod_neg(x);
                lemma_mod_neg(x + 2);
            }
            ComputeIsEven(x + 2)
        }
    }
}

}