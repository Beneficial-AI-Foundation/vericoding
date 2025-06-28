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
    assert(b >= 2);
    assert(b - 1 >= 1);
    assert(b - 1 < b);
    b - 1
}

// Flips a nit: converts n to (b-1-n), essentially inverting the digit
fn nit_flip(b: nat, n: nat) -> (nf: nat)
    requires valid_base(b)
    requires nitness(b, n)
    ensures nitness(b, nf)
    ensures nf == (b - 1) - n
{
    assert(b >= 2);
    assert(n < b);
    assert(b - 1 >= n);
    assert((b - 1) - n < b);
    (b - 1) - n
}

}