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
            assert(digitness(b, sum)) by {
                assert(sum == x + y);
                assert(x < b && y < b);
                assert(sum < b);
            };
            assert(digitness(b, 0)) by {
                assert(0 < b) by {
                    assert(valid_base(b));
                    assert(b >= 2);
                };
            };
            assert(x + y == 0 * b + sum) by {
                assert(0 * b == 0);
                assert(sum == x + y);
            };
        }
        (sum, 0)
    } else {
        let z = sum - b;
        proof {
            // Prove that sum - b < b
            assert(x < b && y < b) by {
                assert(digitness(b, x) && digitness(b, y));
            };
            assert(sum == x + y);
            assert(sum < 2 * b) by {
                assert(x + y < b + b);
            };
            assert(sum >= b);
            assert(z == sum - b);
            assert(z < b) by {
                assert(sum < 2 * b);
                assert(sum >= b);
                assert(z == sum - b);
                assert(z < 2 * b - b);
                assert(z < b);
            };
            
            // Prove digitness properties
            assert(digitness(b, z)) by {
                assert(z < b);
            };
            assert(digitness(b, 1)) by {
                assert(1 < b) by {
                    assert(valid_base(b));
                    assert(b >= 2);
                };
            };
            
            // Prove the mathematical relationship
            assert(x + y == 1 * b + z) by {
                assert(sum == x + y);
                assert(z == sum - b);
                assert(sum == b + z);
                assert(1 * b == b);
                assert(x + y == b + z);
                assert(x + y == 1 * b + z);
            };
        }
        (z, 1)
    }
}

}