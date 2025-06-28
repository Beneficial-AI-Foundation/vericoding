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
fn max_nit(b: u32) -> (nmax: u32)
    requires b >= 2
    ensures (nmax as nat) < (b as nat)
    ensures (nmax as nat) == (b as nat) - 1
{
    b - 1
}

// Flips a nit: converts n to (b-1-n), essentially inverting the digit
fn nit_flip(b: u32, n: u32) -> (nf: u32)
    requires b >= 2
    requires (n as nat) < (b as nat)
    ensures (nf as nat) < (b as nat)
    ensures (nf as nat) == ((b as nat) - 1) - (n as nat)
{
    (b - 1) - n
}

}