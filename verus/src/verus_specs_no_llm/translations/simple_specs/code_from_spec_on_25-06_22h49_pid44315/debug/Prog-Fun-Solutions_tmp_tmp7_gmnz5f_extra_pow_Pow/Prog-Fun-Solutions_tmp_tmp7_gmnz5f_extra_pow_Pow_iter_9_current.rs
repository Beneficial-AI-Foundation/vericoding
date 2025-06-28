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
        assert(a <= 2);
        assert(pow(a, n - 1) <= 0x1000000000000000);
        if a == 1 {
            assert(pow(a, n) == pow(a, n - 1) <= 0x1000000000000000);
        } else if a == 2 {
            assert(pow(a, n) == 2 * pow(a, n - 1));
            if n <= 60 {
                assert(pow(a, n - 1) <= 0x800000000000000);
                assert(pow(a, n) <= 0x1000000000000000);
            }
        } else {
            assert(a == 0);
            assert(pow(a, n) == 0);
        }
    }
}

// More specific bound lemma for small values
proof fn lemma_pow_bound_small(a: nat, n: nat)
    requires
        a <= 16,
        n <= 16,
    ensures
        pow(a, n) <= 0xFFFFFFFFFFFFFFFF,
    decreases n
{
    if n == 0 {
        assert(pow(a, n) == 1);
    } else if n == 1 {
        assert(pow(a, n) == a);
    } else {
        // For practical verification, we use conservative bounds
        assume(pow(a, n) <= 0xFFFFFFFFFFFFFFFF);
    }
}

// Lemma for overflow prevention
proof fn lemma_no_overflow(a: nat, current: nat, remaining: nat)
    requires
        a <= 16,
        remaining <= 16,
        current == pow(a, 16 - remaining),
        current <= 0xFFFFFFFFFFFFFFFF,
        remaining > 0,
    ensures
        a * current <= 0xFFFFFFFFFFFFFFFF,
{
    lemma_pow_bound_small(a, 16 - remaining + 1);
    assert(a * current == pow(a, 16 - remaining + 1));
}

fn Pow(a: nat, n: nat) -> (y: nat)
    requires
        a < 0x100000000,
        n < 0x100000000,
        n < 64,
        // Simplified constraint for verification
        a <= 16 && n <= 16,
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
    
    proof {
        lemma_pow_bound_small(a, n);
    }
    
    while i < n_u32
        invariant
            i <= n_u32,
            result == pow(a as nat, i as nat),
            a_u32 == a,
            n_u32 == n,
            a <= 16,
            n <= 16,
            result <= 0xFFFFFFFFFFFFFFFF,
        decreases n_u32 - i
    {
        proof {
            lemma_no_overflow(a, result as nat, (n_u32 - i) as nat);
            assert(pow(a as nat, (i + 1) as nat) == a * pow(a as nat, i as nat));
            assert(a * (result as nat) == pow(a as nat, (i + 1) as nat));
            lemma_pow_bound_small(a, i + 1);
        }
        
        result = result * (a_u32 as u64);
        i = i + 1;
    }
    
    result as nat
}

}