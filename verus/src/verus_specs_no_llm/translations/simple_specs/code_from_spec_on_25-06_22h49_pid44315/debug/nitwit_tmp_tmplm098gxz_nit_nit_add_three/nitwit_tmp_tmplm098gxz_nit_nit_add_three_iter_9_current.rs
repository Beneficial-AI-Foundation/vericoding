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
    n < b
}

fn nit_add(b: nat, x: nat, y: nat) -> (z: nat, carry: nat)
    requires valid_base(b)
    requires nitness(b, x)
    requires nitness(b, y)
    ensures nitness(b, z)
    ensures nitness(b, carry)
    ensures carry == 0 || carry == 1
    ensures x + y == carry * b + z
{
    let sum = x + y;
    let z = sum % b;
    let carry = sum / b;
    
    // The division theorem gives us sum == carry * b + z automatically
    assert(sum == carry * b + z);
    
    // Prove bounds on sum
    assert(sum < 2 * b) by {
        assert(x < b);
        assert(y < b);
    };
    
    // Prove modulo properties
    assert(z < b);
    
    // Prove division properties for carry
    assert(carry < 2) by {
        // Since sum < 2*b and sum = carry*b + z where z < b
        // We have carry*b + z < 2*b
        // Since z >= 0, we have carry*b <= sum < 2*b
        // Therefore carry < 2
        assert(carry * b <= sum) by {
            assert(sum == carry * b + z);
            assert(z >= 0);
        };
        assert(sum < 2 * b);
        if carry >= 2 {
            assert(carry * b >= 2 * b) by {
                assert(b >= 2);
                assert(carry >= 2);
            };
            assert(false);
        }
    };
    
    assert(carry == 0 || carry == 1) by {
        assert(carry < 2);
        assert(carry >= 0);
    };
    
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
    ensures c + x + y == carry * b + z
{
    let sum = c + x + y;
    let z = sum % b;
    let carry = sum / b;
    
    // The division theorem gives us sum == carry * b + z automatically
    assert(sum == carry * b + z);
    
    // Prove bounds on sum
    assert(sum < 2 * b) by {
        assert(x < b);
        assert(y < b);
        assert(c <= 1);
        // c + x + y <= 1 + (b-1) + (b-1) = 2*b - 1 < 2*b
    };
    
    // Prove modulo properties
    assert(z < b);
    
    // Prove division properties for carry
    assert(carry < 2) by {
        // Since sum < 2*b and sum = carry*b + z where z < b
        // We have carry*b + z < 2*b
        // Since z >= 0, we have carry*b <= sum < 2*b
        // Therefore carry < 2
        assert(carry * b <= sum) by {
            assert(sum == carry * b + z);
            assert(z >= 0);
        };
        assert(sum < 2 * b);
        if carry >= 2 {
            assert(carry * b >= 2 * b) by {
                assert(b >= 2);
                assert(carry >= 2);
            };
            assert(false);
        }
    };
    
    assert(carry == 0 || carry == 1) by {
        assert(carry < 2);
        assert(carry >= 0);
    };
    
    (z, carry)
}

}