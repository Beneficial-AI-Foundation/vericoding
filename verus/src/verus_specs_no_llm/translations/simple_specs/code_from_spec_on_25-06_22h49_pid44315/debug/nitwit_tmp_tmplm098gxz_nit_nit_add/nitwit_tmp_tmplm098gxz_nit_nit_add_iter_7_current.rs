use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn digitness(b: nat, n: nat) -> bool 
    requires valid_base(b)
{
    n < b
}

spec fn valid_base(b: nat) -> bool {
    b >= 2
}

fn nit_add(b: nat, x: nat, y: nat) -> (z: nat, carry: nat)
    requires
        valid_base(b),
        digitness(b, x),
        digitness(b, y)
    ensures
        digitness(b, z),
        digitness(b, carry),
        // This is a useful fact for doing general form addition.
        carry == 0 || carry == 1,
        // The mathematical relationship
        x + y == carry * b + z
{
    let sum = x + y;
    if sum < b {
        (sum, 0)
    } else {
        let z = sum - b;
        (z, 1)
    }
}

}