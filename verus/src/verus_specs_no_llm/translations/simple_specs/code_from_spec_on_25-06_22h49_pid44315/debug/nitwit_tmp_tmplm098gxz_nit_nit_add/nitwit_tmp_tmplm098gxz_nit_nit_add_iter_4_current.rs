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
        proof {
            // Prove that sum < b implies carry == 0 and z == sum
            assert(sum == 0 * b + sum) by {
                assert(0 * b == 0);
            }
            assert(digitness(b, sum)) by {
                assert(sum < b);
            }
            assert(digitness(b, 0)) by {
                assert(valid_base(b));
                assert(b >= 2);
                assert(0 < 2);
                assert(0 < b);
            }
        }
        (sum, 0)
    } else {
        proof {
            // Prove that sum >= b implies carry == 1 and z == sum - b
            assert(sum >= b);
            
            // Prove that sum - b < b
            assert(sum - b < b) by {
                // Since x < b and y < b, we have x + y < 2*b
                // So sum - b < b
                assert(x < b) by {
                    assert(digitness(b, x));
                }
                assert(y < b) by {
                    assert(digitness(b, y));
                }
                assert(x + y < b + b) by {
                    // This follows from x < b and y < b
                    assert(x + y == (x) + (y));
                    assert((x) + (y) < b + b);
                }
                assert(sum < 2 * b) by {
                    assert(sum == x + y);
                }
                // Now sum >= b and sum < 2*b, so sum - b < b
                assert(sum < 2 * b);
                assert(sum >= b);
                // Therefore sum - b < 2*b - b = b
            }
            
            // Prove digitness properties
            assert(digitness(b, sum - b)) by {
                assert(sum - b < b);
            }
            assert(digitness(b, 1)) by {
                assert(valid_base(b));
                assert(b >= 2);
                assert(1 < 2);
                assert(1 < b);
            }
            
            // Prove the mathematical relationship
            assert(sum == 1 * b + (sum - b)) by {
                assert(1 * b == b);
            }
        }
        (sum - b, 1)
    }
}

}