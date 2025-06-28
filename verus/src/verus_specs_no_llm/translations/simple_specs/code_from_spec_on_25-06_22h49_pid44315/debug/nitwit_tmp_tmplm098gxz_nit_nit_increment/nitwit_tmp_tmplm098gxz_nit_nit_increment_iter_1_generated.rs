use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn nitness(b: nat, n: nat) -> bool
    requires valid_base(b)
{
    0 <= n < b
}

spec fn valid_base(b: nat) -> bool {
    b >= 2
}

fn nit_increment(b: nat, n: nat) -> (sum: nat, carry: nat)
    requires 
        valid_base(b),
        nitness(b, n)
    ensures
        nitness(b, sum),
        nitness(b, carry)
{
    if n + 1 < b {
        // No carry needed
        ((n + 1) as nat, 0nat)
    } else {
        // Carry needed: n + 1 == b, so sum = 0, carry = 1
        (0nat, 1nat)
    }
}

}