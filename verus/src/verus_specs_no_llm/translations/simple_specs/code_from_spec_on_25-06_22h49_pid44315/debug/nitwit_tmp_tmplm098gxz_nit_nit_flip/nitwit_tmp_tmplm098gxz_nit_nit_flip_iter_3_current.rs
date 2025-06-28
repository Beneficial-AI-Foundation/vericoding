use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// A valid base must be at least 2
spec fn valid_base(b: nat) -> bool {
    b >= 2
}

// A number n is a "nit" in base b if it's a valid digit in that base
spec fn nitness(b: nat, n: nat) -> bool
    requires valid_base(b)
{
    n < b
}

// Check if a number is the maximum nit (digit) in a given base
spec fn is_max_nit(b: nat, q: nat) -> bool {
    q == b - 1
}

// Returns the maximum nit (digit) for a given base
fn max_nit(b: nat) -> (nmax: nat)
    requires valid_base(b)
    ensures nitness(b, nmax)
    ensures is_max_nit(b, nmax)
{
    // Prove that b - 1 is well-defined and satisfies the postconditions
    assert(b >= 2);
    assert(b >= 1);  // This ensures b - 1 >= 0, so subtraction is safe
    let result = (b - 1) as nat;
    assert(result < b);  // This proves nitness(b, result)
    assert(result == b - 1);  // This proves is_max_nit(b, result)
    result
}

// Flips a nit: converts n to (b-1-n), essentially inverting the digit
fn nit_flip(b: nat, n: nat) -> (nf: nat)
    requires valid_base(b)
    requires nitness(b, n)
    ensures nitness(b, nf)
    ensures nf == (b - 1) - n
{
    // Prove that the subtraction is well-defined
    assert(b >= 2);
    assert(n < b);
    assert(b >= 1);  // Ensures b - 1 >= 0
    assert(n <= b - 1);  // Since n < b and both are naturals
    assert(b - 1 >= n);  // This ensures (b - 1) - n >= 0
    
    let result = ((b - 1) - n) as nat;
    
    // Prove nitness(b, result): result < b
    assert(result == (b - 1) - n);
    assert(result <= b - 1);  // Since n >= 0, (b-1) - n <= b-1
    assert(result < b);  // Since b-1 < b
    
    result
}

}