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
{
    let sum = x + y;
    let z = sum % b;
    let carry = sum / b;
    
    // Prove bounds on sum
    assert(x < b && y < b);
    assert(sum < 2 * b);
    
    // Prove modulo properties
    assert(z < b);
    
    // Prove division properties for carry
    assert(carry == 0 || carry == 1) by {
        // Since sum < 2*b, we have sum/b < 2
        // Since carry is nat (>= 0) and carry < 2, carry must be 0 or 1
        assert(sum < 2 * b);
        
        // Use the fundamental division property
        assert(sum == carry * b + z);
        assert(z < b);
        
        if sum < b {
            // If sum < b, then sum/b = 0
            assert(carry == 0);
        } else {
            // If sum >= b and sum < 2*b, then sum/b = 1
            assert(sum >= b);
            assert(sum < 2 * b);
            // Since sum = carry*b + z and z < b:
            // If carry >= 2, then carry*b >= 2*b, so sum >= 2*b, contradiction
            // If carry = 0, then sum = z < b, contradicting sum >= b
            // Therefore carry = 1
            assert(carry == 1);
        }
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
{
    let sum = c + x + y;
    let z = sum % b;
    let carry = sum / b;
    
    // Prove bounds on sum
    assert(x < b && y < b && c <= 1);
    assert(sum <= 2 * b - 1) by {
        // c <= 1, x < b, y < b means x <= b-1, y <= b-1
        // so c + x + y <= 1 + (b-1) + (b-1) = 2*b - 1
        assert(x <= b - 1);
        assert(y <= b - 1);
        assert(c + x + y <= 1 + (b - 1) + (b - 1));
        assert(1 + (b - 1) + (b - 1) == 2 * b - 1);
    };
    assert(sum < 2 * b) by {
        assert(sum <= 2 * b - 1);
    };
    
    // Prove modulo properties
    assert(z < b);
    
    // Prove division properties for carry
    assert(carry == 0 || carry == 1) by {
        assert(sum < 2 * b);
        
        // Use the fundamental division property
        assert(sum == carry * b + z);
        assert(z < b);
        
        if sum < b {
            // If sum < b, then sum/b = 0
            assert(carry == 0);
        } else {
            // If sum >= b and sum < 2*b, then sum/b = 1
            assert(sum >= b);
            assert(sum < 2 * b);
            // Since sum = carry*b + z and z < b:
            // If carry >= 2, then carry*b >= 2*b, so sum >= 2*b, contradiction
            // If carry = 0, then sum = z < b, contradicting sum >= b
            // Therefore carry = 1
            assert(carry == 1);
        }
    };
    
    (z, carry)
}

}