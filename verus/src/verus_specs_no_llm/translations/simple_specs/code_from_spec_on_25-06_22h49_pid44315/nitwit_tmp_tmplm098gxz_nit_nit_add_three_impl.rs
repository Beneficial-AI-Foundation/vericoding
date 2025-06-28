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
    
    // Prove bounds on sum first
    assert(sum < 2 * b) by {
        assert(x < b);
        assert(y < b);
        assert(x + y < b + b);
    };
    
    // Use division theorem: for any natural numbers a and b with b > 0,
    // a == (a / b) * b + (a % b)
    assert(sum == carry * b + z) by {
        // This follows from the division theorem
    };
    
    // z is the remainder, so z < b
    assert(z < b) by {
        // This follows from the definition of modulo
    };
    
    // Prove carry bounds
    assert(carry <= 1) by {
        // Since sum < 2*b and sum = carry*b + z where 0 <= z < b
        // If carry >= 2, then carry*b >= 2*b, but carry*b <= sum < 2*b
        // This is a contradiction
        if carry >= 2 {
            assert(carry * b >= 2 * b) by {
                assert(b >= 2);
                assert(carry >= 2);
            };
            assert(carry * b + z >= 2 * b) by {
                assert(z >= 0);
            };
            assert(sum >= 2 * b);
            assert(false); // contradiction with sum < 2*b
        }
    };
    
    assert(carry >= 0);
    assert(carry == 0 || carry == 1) by {
        assert(carry <= 1);
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
    
    // Prove bounds on sum first
    assert(sum <= 2 * b - 1) by {
        assert(x < b);
        assert(y < b);
        assert(c <= 1);
        // c + x + y <= 1 + (b-1) + (b-1) = 2*b - 1
        assert(x <= b - 1);
        assert(y <= b - 1);
        assert(c + x + y <= 1 + (b - 1) + (b - 1));
        assert(1 + (b - 1) + (b - 1) == 2 * b - 1);
    };
    
    assert(sum < 2 * b) by {
        assert(sum <= 2 * b - 1);
        assert(2 * b - 1 < 2 * b);
    };
    
    // Use division theorem
    assert(sum == carry * b + z) by {
        // This follows from the division theorem
    };
    
    // z is the remainder, so z < b
    assert(z < b) by {
        // This follows from the definition of modulo
    };
    
    // Prove carry bounds
    assert(carry <= 1) by {
        // Since sum < 2*b and sum = carry*b + z where 0 <= z < b
        // If carry >= 2, then carry*b >= 2*b, but carry*b <= sum < 2*b
        // This is a contradiction
        if carry >= 2 {
            assert(carry * b >= 2 * b) by {
                assert(b >= 2);
                assert(carry >= 2);
            };
            assert(carry * b + z >= 2 * b) by {
                assert(z >= 0);
            };
            assert(sum >= 2 * b);
            assert(false); // contradiction with sum < 2*b
        }
    };
    
    assert(carry >= 0);
    assert(carry == 0 || carry == 1) by {
        assert(carry <= 1);
        assert(carry >= 0);
    };
    
    (z, carry)
}

}