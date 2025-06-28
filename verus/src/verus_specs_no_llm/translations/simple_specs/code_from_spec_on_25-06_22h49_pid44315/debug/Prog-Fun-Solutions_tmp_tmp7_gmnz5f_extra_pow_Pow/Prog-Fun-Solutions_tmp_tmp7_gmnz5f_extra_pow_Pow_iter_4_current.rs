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

fn Pow(a: nat, n: nat) -> (y: nat)
    requires
        a < 0x100000000,
        n < 0x100000000,
    ensures
        y == pow(a, n)
{
    let mut result: u64 = 1;
    let mut i: u32 = 0;
    let a_u32: u32 = a as u32;
    let n_u32: u32 = n as u32;
    
    while i < n_u32
        invariant
            i <= n_u32,
            result == pow(a, i as nat),
            a_u32 == a,
            n_u32 == n,
            result < 0x10000000000000000, // bound to prevent overflow
        decreases n_u32 - i
    {
        proof {
            // Prove that multiplication won't overflow
            assert(result <= pow(a, i as nat));
            assert(a < 0x100000000);
            assert(i < n);
            assert(n < 0x100000000);
        }
        result = result * (a_u32 as u64);
        i = i + 1;
    }
    
    result as nat
}

}