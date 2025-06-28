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
            // When sum < b, we return (sum, 0)
            // We need to prove: digitness(b, sum), digitness(b, 0), 0 == 0 || 0 == 1, x + y == 0 * b + sum
            assert(sum == x + y);
            assert(sum < b);
            assert(0 < b); // since valid_base(b) implies b >= 2
        }
        (sum, 0)
    } else {
        let z = sum - b;
        proof {
            // When sum >= b, we return (sum - b, 1)
            // We need to prove: digitness(b, z), digitness(b, 1), 1 == 0 || 1 == 1, x + y == 1 * b + z
            assert(sum >= b);
            assert(sum == x + y);
            assert(z == sum - b);
            assert(x + y == sum);
            assert(sum == b + z); // since z = sum - b, we have sum = b + z
            assert(x + y == b + z);
            assert(x + y == 1 * b + z);
            
            // Prove digitness(b, z): z < b
            // We know x < b and y < b, so x + y < 2*b
            // Since sum >= b and sum < 2*b, we have z = sum - b < b
            assert(x < b && y < b); // from digitness preconditions
            assert(x + y < 2 * b); // since x < b and y < b
            assert(sum < 2 * b);
            assert(z < b); // since z = sum - b and sum < 2*b
            
            // Prove digitness(b, 1): 1 < b
            assert(b >= 2); // from valid_base(b)
            assert(1 < b);
        }
        (z, 1)
    }
}

}