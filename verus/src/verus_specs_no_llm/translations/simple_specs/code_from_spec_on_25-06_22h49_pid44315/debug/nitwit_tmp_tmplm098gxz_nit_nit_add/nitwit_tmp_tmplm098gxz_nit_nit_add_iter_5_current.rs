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
            assert(digitness(b, sum));
            assert(digitness(b, 0));
            assert(x + y == 0 * b + sum);
        }
        (sum, 0)
    } else {
        let z = sum - b;
        proof {
            // Prove that sum - b < b
            assert(x < b);
            assert(y < b);
            assert(sum == x + y);
            assert(sum < 2 * b);
            assert(sum >= b);
            assert(z < b);
            
            // Prove digitness properties
            assert(digitness(b, z));
            assert(digitness(b, 1));
            
            // Prove the mathematical relationship
            assert(x + y == 1 * b + z);
        }
        (z, 1)
    }
}

}