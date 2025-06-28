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
    
    // Prove bounds on sum
    assert(x < b && y < b);
    assert(sum < 2 * b) by {
        assert(x < b);
        assert(y < b);
        assert(x + y < b + b);
    };
    
    // Prove modulo properties
    assert(z < b) by {
        assert(sum % b < b);
    };
    
    // Prove division properties for carry
    assert(carry == 0 || carry == 1) by {
        assert(sum < 2 * b);
        assert(sum == carry * b + z) by {
            // This is the fundamental division theorem
        };
        assert(z < b);
        
        if carry >= 2 {
            assert(carry * b >= 2 * b) by {
                assert(carry >= 2);
                assert(b >= 2);
                assert(2 * b <= carry * b);
            };
            assert(sum >= carry * b) by {
                assert(sum == carry * b + z);
                assert(z >= 0);
            };
            assert(sum >= 2 * b);
            assert(false); // contradiction with sum < 2 * b
        }
        
        if carry == 0 {
            assert(sum == z);
            assert(sum < b);
        } else {
            assert(carry == 1) by {
                assert(carry >= 1);
                assert(carry < 2);
            };
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
    ensures c + x + y == carry * b + z
{
    let sum = c + x + y;
    let z = sum % b;
    let carry = sum / b;
    
    // Prove bounds on sum
    assert(x < b && y < b && c <= 1);
    assert(sum <= 2 * b - 1) by {
        assert(x <= b - 1) by {
            assert(x < b);
            assert(x + 1 <= b);
        };
        assert(y <= b - 1) by {
            assert(y < b);
            assert(y + 1 <= b);
        };
        assert(c + x + y <= 1 + (b - 1) + (b - 1));
        assert(1 + (b - 1) + (b - 1) == 2 * b - 1) by {
            assert(1 + b - 1 + b - 1 == b + b - 1);
            assert(b + b - 1 == 2 * b - 1);
        };
    };
    assert(sum < 2 * b) by {
        assert(sum <= 2 * b - 1);
        assert(2 * b - 1 < 2 * b) by {
            assert(2 * b >= 1) by {
                assert(b >= 2);
                assert(2 * b >= 4);
            };
        };
    };
    
    // Prove modulo properties
    assert(z < b) by {
        assert(sum % b < b);
    };
    
    // Prove division properties for carry
    assert(carry == 0 || carry == 1) by {
        assert(sum < 2 * b);
        assert(sum == carry * b + z) by {
            // This is the fundamental division theorem
        };
        assert(z < b);
        
        if carry >= 2 {
            assert(carry * b >= 2 * b) by {
                assert(carry >= 2);
                assert(b >= 2);
                assert(2 * b <= carry * b);
            };
            assert(sum >= carry * b) by {
                assert(sum == carry * b + z);
                assert(z >= 0);
            };
            assert(sum >= 2 * b);
            assert(false); // contradiction with sum < 2 * b
        }
        
        if carry == 0 {
            assert(sum == z);
            assert(sum < b);
        } else {
            assert(carry == 1) by {
                assert(carry >= 1);
                assert(carry < 2);
            };
        }
    };
    
    (z, carry)
}

}