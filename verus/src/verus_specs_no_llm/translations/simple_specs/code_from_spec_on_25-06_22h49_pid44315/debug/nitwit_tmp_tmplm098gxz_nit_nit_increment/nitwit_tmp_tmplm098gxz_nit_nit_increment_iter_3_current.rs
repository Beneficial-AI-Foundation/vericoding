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

fn nit_increment(b: nat, n: nat) -> (sum: nat, carry: nat)
    requires 
        valid_base(b),
        nitness(b, n)
    ensures
        nitness(b, sum),
        nitness(b, carry)
{
    if n + 1 < b {
        // No carry needed
        let sum = n + 1;
        let carry = 0;
        
        assert(sum < b);
        assert(carry == 0);
        assert(carry < b) by {
            assert(valid_base(b));
            assert(b >= 2);
            assert(0 < 2);
            assert(0 < b);
        };
        
        (sum, carry)
    } else {
        // Carry needed: n + 1 >= b, so sum = 0, carry = 1
        let sum = 0;
        let carry = 1;
        
        assert(n + 1 >= b);
        assert(nitness(b, n));
        assert(n < b);
        assert(n + 1 == b) by {
            // Since n < b and n + 1 >= b, we must have n + 1 == b
            assert(n < b);
            assert(n + 1 >= b);
        };
        
        assert(sum == 0);
        assert(sum < b) by {
            assert(valid_base(b));
            assert(b >= 2);
            assert(0 < 2);
            assert(0 < b);
        };
        
        assert(carry == 1);
        assert(carry < b) by {
            assert(valid_base(b));
            assert(b >= 2);
            assert(1 < 2);
            assert(1 < b);
        };
        
        (sum, carry)
    }
}

}

The key fixes:

This should now verify successfully as Verus can follow the logical steps to prove that both `sum` and `carry` satisfy the `nitness` property.