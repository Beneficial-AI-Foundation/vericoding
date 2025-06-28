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
    
    // Prove bounds on sum
    assert(x < b && y < b);
    assert(sum < 2 * b) by {
        assert(x + y < b + b);
    };
    
    // Prove division and modulo properties
    assert(z < b) by {
        // modulo operation ensures remainder is less than divisor
    };
    assert(z >= 0);
    
    assert(carry < 2) by {
        // Since sum < 2*b and sum = carry*b + z where z < b
        // We have carry*b < sum < 2*b, so carry < 2
        assert(sum == carry * b + z);
        assert(z < b);
        assert(sum < 2 * b);
        if carry >= 2 {
            assert(carry * b >= 2 * b);
            assert(sum >= carry * b >= 2 * b);
            assert(false);
        }
    };
    assert(carry >= 0);
    
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
    
    // Prove bounds on sum
    assert(x < b && y < b && c <= 1);
    assert(sum < 2 * b) by {
        assert(c + x + y <= 1 + (b - 1) + (b - 1));
        assert(sum <= 2 * b - 1);
    };
    
    // Prove division and modulo properties
    assert(z < b) by {
        // modulo operation ensures remainder is less than divisor
    };
    assert(z >= 0);
    
    assert(carry < 2) by {
        // Since sum < 2*b and sum = carry*b + z where z < b
        // We have carry*b < sum < 2*b, so carry < 2
        assert(sum == carry * b + z);
        assert(z < b);
        assert(sum < 2 * b);
        if carry >= 2 {
            assert(carry * b >= 2 * b);
            assert(sum >= carry * b >= 2 * b);
            assert(false);
        }
    };
    assert(carry >= 0);
    
    (z, carry)
}

}