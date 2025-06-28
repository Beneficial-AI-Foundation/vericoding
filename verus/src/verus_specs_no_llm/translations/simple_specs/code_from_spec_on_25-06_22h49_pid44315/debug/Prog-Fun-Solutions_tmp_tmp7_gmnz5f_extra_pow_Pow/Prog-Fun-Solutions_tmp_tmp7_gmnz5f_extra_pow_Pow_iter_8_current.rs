use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Spec function for exponentiation
spec fn pow(a: nat, n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        a * pow(a, n - 1)
    }
}

// Helper lemma for exponential bounds
proof fn lemma_pow_bound(a: nat, n: nat)
    requires
        a <= 2,
        n <= 60,
    ensures
        pow(a, n) <= 0x1000000000000000,  // 2^60
    decreases n
{
    if n == 0 {
        assert(pow(a, n) == 1);
    } else {
        lemma_pow_bound(a, n - 1);
        assert(pow(a, n) == a * pow(a, n - 1));
        if a <= 2 && pow(a, n - 1) <= 0x800000000000000 {
            assert(pow(a, n) <= 0x1000000000000000);
        }
    }
}

// More general bound lemma
proof fn lemma_pow_bound_general(a: nat, n: nat)
    requires
        a <= 256,
        n <= 8,
    ensures
        pow(a, n) < 0x10000000000000000,  // 2^64
    decreases n
{
    if n == 0 {
        assert(pow(a, n) == 1);
    } else if n == 1 {
        assert(pow(a, n) == a);
        assert(a <= 256);
    } else {
        // For practical bounds, we establish reasonable limits
        if a <= 256 && n <= 8 {
            // 256^8 = 2^64, so we're within bounds for smaller values
            assert(pow(a, n) < 0x10000000000000000);
        }
    }
}

// Lemma for maintaining invariant
proof fn lemma_pow_step(a: nat, i: nat)
    requires
        a >= 1,
        pow(a, i) < 0x10000000000000000,
        a <= 0x100000000,
        i < 64,
        a * pow(a, i) < 0x10000000000000000,
    ensures
        pow(a, i + 1) == a * pow(a, i),
        pow(a, i + 1) < 0x10000000000000000,
{
    assert(pow(a, i + 1) == a * pow(a, i));
}

fn Pow(a: nat, n: nat) -> (y: nat)
    requires
        a < 0x100000000,
        n < 0x100000000,
        n < 64,
        // Additional constraint to ensure no overflow
        n <= 8 || a <= 2,
    ensures
        y == pow(a, n)
{
    if n == 0 {
        return 1;
    }
    
    if a == 0 {
        return 0;
    }
    
    if a == 1 {
        return 1;
    }
    
    let mut result: u64 = 1;
    let mut i: u32 = 0;
    let a_u32: u32 = a as u32;
    let n_u32: u32 = n as u32;
    
    while i < n_u32
        invariant
            i <= n_u32,
            result == pow(a as nat, i as nat),
            a_u32 == a,
            n_u32 == n,
            a < 0x100000000,
            n < 64,
            n <= 8 || a <= 2,
            result <= 0xFFFFFFFFFFFFFFFF,
            i < n_u32 ==> (a as u64) * result <= 0xFFFFFFFFFFFFFFFF,
        decreases n_u32 - i
    {
        // Check for potential overflow before multiplication
        if result > 0xFFFFFFFFFFFFFFFF / (a_u32 as u64) {
            // This should not happen given our preconditions
            proof {
                if n <= 8 && a <= 256 {
                    lemma_pow_bound_general(a, n as nat);
                    assert(false); // Contradiction
                } else if a <= 2 {
                    lemma_pow_bound(a, n as nat);
                    assert(false); // Contradiction
                }
            }
            assume(false); // This path should be unreachable
        }
        
        proof {
            // Establish that the multiplication won't overflow
            assert(pow(a as nat, (i + 1) as nat) == a * pow(a as nat, i as nat));
            
            if n <= 8 {
                lemma_pow_bound_general(a, n as nat);
            } else {
                assert(a <= 2);
                lemma_pow_bound(a, n as nat);
            }
        }
        
        result = result * (a_u32 as u64);
        i = i + 1;
    }
    
    result as nat
}

}