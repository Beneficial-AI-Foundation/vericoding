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
        (sum, 0)
    } else {
        let z = sum - b;
        
        // Prove that z < b (digitness)
        assert(sum >= b);
        assert(x < b && y < b) by {
            assert(digitness(b, x));
            assert(digitness(b, y));
        };
        assert(sum == x + y);
        assert(x + y < 2 * b) by {
            // Since x < b and y < b, we have x + y < b + b = 2*b
            assert(x < b);
            assert(y < b);
        };
        assert(sum < 2 * b);
        assert(z == sum - b);
        assert(z < b) by {
            // z = sum - b < 2*b - b = b
            assert(sum < 2 * b);
            assert(z == sum - b);
        };
        
        // Prove that carry is valid (0 or 1, and digitness)
        assert(1 < b) by {
            assert(valid_base(b));
            assert(b >= 2);
        };
        
        // Prove the mathematical relationship
        assert(sum == b + z) by {
            assert(z == sum - b);
        };
        assert(x + y == 1 * b + z) by {
            assert(sum == x + y);
            assert(sum == b + z);
        };
        
        (z, 1)
    }
}

}