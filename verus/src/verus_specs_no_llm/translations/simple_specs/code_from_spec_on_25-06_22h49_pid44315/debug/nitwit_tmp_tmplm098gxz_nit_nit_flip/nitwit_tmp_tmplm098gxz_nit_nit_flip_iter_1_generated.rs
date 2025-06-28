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
    0 <= n < b
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
    b - 1
}

// Flips a nit: converts n to (b-1-n), essentially inverting the digit
fn nit_flip(b: nat, n: nat) -> (nf: nat)
    requires valid_base(b)
    requires nitness(b, n)
    ensures nitness(b, nf)
    ensures nf == (b - 1) - n
{
    (b - 1) - n
}

}

Key fixes made:

6. **Cleaned up specifications** - Used consistent `spec fn` syntax and proper logical structure

The implementation satisfies all the mathematical properties:
- `valid_base(b)` ensures `b >= 2`
- `nitness(b, n)` ensures `0 <= n < b` (n is a valid digit in base b)
- `is_max_nit(b, q)` ensures `q == b - 1` (q is the largest digit in base b)
- `max_nit(b)` returns the maximum digit for base b
- `nit_flip(b, n)` returns the "flipped" version of digit n in base b