use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn StarNumber(n: int) -> int
    requires
        n >= 0
{
    6 * n * (n - 1) + 1
}

// Helper lemma to prove properties about star numbers
proof fn lemma_star_number_properties(n: int)
    requires n >= 0
    ensures StarNumber(n) >= 1
    ensures n == 0 ==> StarNumber(n) == 1
    ensures n >= 1 ==> StarNumber(n) > 1
{
    // The proof is straightforward from the definition
    assert(StarNumber(n) == 6 * n * (n - 1) + 1);
    
    if n == 0 {
        assert(6 * 0 * (0 - 1) == 0);
        assert(StarNumber(0) == 0 + 1 == 1);
    } else {
        // n >= 1
        assert(n >= 1);
        if n == 1 {
            assert(6 * 1 * (1 - 1) == 0);
            assert(StarNumber(1) == 0 + 1 == 1);
        } else {
            // n >= 2, so n - 1 >= 1
            assert(n >= 2);
            assert(n - 1 >= 1);
            assert(6 * n * (n - 1) >= 6 * 2 * 1);
            assert(6 * n * (n - 1) >= 12);
            assert(StarNumber(n) >= 12 + 1);
            assert(StarNumber(n) >= 13);
            assert(StarNumber(n) > 1);
        }
    }
}

// Example function that uses StarNumber to demonstrate it works
fn compute_star_number(n: u32) -> (result: u64)
    requires n <= 1000  // reasonable bound to prevent overflow
    ensures result == StarNumber(n as int)
{
    if n == 0 {
        proof {
            assert(StarNumber(0) == 6 * 0 * (0 - 1) + 1 == 1);
        }
        1u64
    } else {
        let n_u64 = n as u64;
        let n_minus_1 = (n - 1) as u64;
        let star_num = 6u64 * n_u64 * n_minus_1 + 1u64;
        
        proof {
            // Prove that our computation matches the spec
            assert(n_u64 == n as u64);
            assert(n_minus_1 == (n - 1) as u64);
            assert(n_minus_1 == (n as int - 1) as u64);
            assert(star_num == 6 * (n as int) * ((n as int) - 1) + 1);
            assert(star_num == StarNumber(n as int));
        }
        
        star_num
    }
}

}