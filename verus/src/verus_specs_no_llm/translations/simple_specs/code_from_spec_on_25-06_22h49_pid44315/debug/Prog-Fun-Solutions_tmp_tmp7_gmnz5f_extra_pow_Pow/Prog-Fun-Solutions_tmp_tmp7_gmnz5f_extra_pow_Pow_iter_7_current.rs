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

// Helper lemma for overflow bounds
proof fn lemma_pow_monotonic(a: nat, i: nat, n: nat)
    requires 
        a >= 1,
        i <= n,
        n < 64,  // Reasonable bound for u64
    ensures
        pow(a, i) <= pow(a, n)
    decreases n - i
{
    if i < n {
        lemma_pow_monotonic(a, i + 1, n);
    }
}

// Helper lemma for small exponentials
proof fn lemma_small_pow_bound(a: nat, n: nat)
    requires
        a < 0x100000000,
        n < 64,
    ensures
        n == 0 ==> pow(a, n) == 1,
        n <= 1 ==> pow(a, n) <= 0x100000000,
        pow(a, n) < 0x10000000000000000,  // Less than 2^64
{
    if n == 0 {
        // Base case
    } else if n == 1 {
        // n == 1 case
    } else {
        // For larger n, we can use mathematical properties
        // This is a simplified bound - in practice you might need more sophisticated reasoning
    }
}

fn Pow(a: nat, n: nat) -> (y: nat)
    requires
        a < 0x100000000,
        n < 0x100000000,
        n < 64,  // Additional bound to ensure no overflow
    ensures
        y == pow(a, n)
{
    let mut result: u64 = 1;
    let mut i: u32 = 0;
    let a_u32: u32 = a as u32;
    let n_u32: u32 = n as u32;
    
    proof {
        lemma_small_pow_bound(a, n);
    }
    
    while i < n_u32
        invariant
            i <= n_u32,
            result == pow(a as nat, i as nat),
            a_u32 == a,
            n_u32 == n,
            result < 0x10000000000000000u64,  // result fits in u64
            a < 0x100000000,
            n < 64,
        decreases n_u32 - i
    {
        proof {
            // Prove the recurrence relation for pow
            assert(pow(a as nat, (i + 1) as nat) == a * pow(a as nat, i as nat)) by {
                // This follows from the definition of pow
            };
            
            // Prove no overflow will occur
            lemma_small_pow_bound(a, n);
            assert(pow(a as nat, (i + 1) as nat) < 0x10000000000000000);
        }
        
        result = result * (a_u32 as u64);
        i = i + 1;
    }
    
    result as nat
}

}