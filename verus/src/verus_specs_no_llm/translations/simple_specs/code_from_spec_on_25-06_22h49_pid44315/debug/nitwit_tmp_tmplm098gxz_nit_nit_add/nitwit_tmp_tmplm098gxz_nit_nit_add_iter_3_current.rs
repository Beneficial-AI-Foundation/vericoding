use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn nitness(b: nat, n: nat) -> bool 
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
        nitness(b, x),
        nitness(b, y)
    ensures
        nitness(b, z),
        nitness(b, carry),
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
                assert(0 + sum == sum);
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
                assert(x < b);
                assert(y < b);
                assert(x + y < b + b) by {
                    // This follows from x < b and y < b
                }
                assert(sum < 2 * b) by {
                    assert(sum == x + y);
                    assert(2 * b == b + b);
                }
                // Now sum >= b and sum < 2*b, so sum - b < b
                assert(sum - b < 2 * b - b);
                assert(2 * b - b == b);
            }
            
            // Prove the mathematical relationship
            assert(sum == 1 * b + (sum - b)) by {
                assert(1 * b == b);
                assert(b + (sum - b) == sum);
            }
        }
        (sum - b, 1)
    }
}

}