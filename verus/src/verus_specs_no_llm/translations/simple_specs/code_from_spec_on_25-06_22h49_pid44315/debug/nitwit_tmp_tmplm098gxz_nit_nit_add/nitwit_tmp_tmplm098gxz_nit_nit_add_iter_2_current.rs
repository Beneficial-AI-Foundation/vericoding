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
            assert(sum == 0 * b + sum);
        }
        (sum, 0)
    } else {
        proof {
            // Prove that sum >= b implies carry == 1 and z == sum - b
            assert(sum >= b);
            assert(sum - b < b) by {
                // Since x < b and y < b, we have x + y < 2*b
                // So sum - b < b
                assert(x < b);
                assert(y < b);
                assert(sum < 2 * b);
                assert(sum - b < b);
            }
            assert(sum == 1 * b + (sum - b));
        }
        (sum - b, 1)
    }
}

}