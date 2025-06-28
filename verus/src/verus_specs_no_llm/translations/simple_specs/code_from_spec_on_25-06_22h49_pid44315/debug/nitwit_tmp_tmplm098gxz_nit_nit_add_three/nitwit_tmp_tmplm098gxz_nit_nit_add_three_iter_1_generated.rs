use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn valid_base(b: nat) -> bool {
    b >= 2
}

spec fn nitness(b: nat, n: nat) -> bool
    requires valid_base(b)
{
    0 <= n < b
}

fn nit_add(b: nat, x: nat, y: nat) -> (z: nat, carry: nat)
    requires valid_base(b)
    requires nitness(b, x)
    requires nitness(b, y)
    ensures nitness(b, z)
    ensures nitness(b, carry)
    ensures carry == 0 || carry == 1
{
    let sum = x + y;
    let z = sum % b;
    let carry = sum / b;
    
    // The carry can only be 0 or 1 since x < b and y < b, so x + y < 2*b
    assert(sum < 2 * b);
    assert(carry < 2);
    assert(carry == 0 || carry == 1);
    
    (z, carry)
}

fn nit_add_three(b: nat, c: nat, x: nat, y: nat) -> (z: nat, carry: nat)
    requires valid_base(b)
    requires nitness(b, x)
    requires nitness(b, y)
    requires c == 0 || c == 1
    ensures nitness(b, z)
    ensures nitness(b, carry)
    ensures carry == 0 || carry == 1
{
    let sum = c + x + y;
    let z = sum % b;
    let carry = sum / b;
    
    // The carry can only be 0, 1, or 2 since c <= 1, x < b, y < b
    // But we need to prove it's only 0 or 1
    assert(sum <= 1 + (b - 1) + (b - 1));
    assert(sum <= 2 * b - 1);
    assert(sum < 2 * b);
    assert(carry < 2);
    assert(carry == 0 || carry == 1);
    
    (z, carry)
}

}