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
        assert(n + 1 < b);
        assert(carry < b) by {
            assert(valid_base(b));
            assert(b >= 2);
            assert(0 < b);
        }
        (n + 1, 0)
    } else {
        // Carry needed: n + 1 >= b, so sum = 0, carry = 1
        assert(n + 1 >= b);
        assert(nitness(b, n));
        assert(n < b);
        assert(n + 1 == b) by {
            // Since n < b and n + 1 >= b, we must have n + 1 == b
        }
        assert(0 < b);
        assert(1 < b) by {
            assert(valid_base(b));
            assert(b >= 2);
        }
        (0, 1)
    }
}

}

The key changes made:



   - In the no-carry case: `carry = 0 < b` (using the fact that `b >= 2`)
   - In the carry case: `sum = 0 < b` and `carry = 1 < b` (using the fact that `b >= 2`)


The proof assertions help Verus understand why the postconditions `nitness(b, sum)` and `nitness(b, carry)` are satisfied in both branches of the conditional.