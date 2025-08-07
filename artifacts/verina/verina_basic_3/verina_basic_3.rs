use vstd::prelude::*;

verus! {

spec fn is_divisible_by_11_precond(n: int) -> bool {
    true
}

fn is_divisible_by_11(n: i64) -> (result: bool)
    requires is_divisible_by_11_precond(n as int)
    ensures (result ==> exists|k: int| #[trigger] (11 * k) == n as int) &&
            (!result ==> forall|k: int| #[trigger] (11 * k) != n as int)
{
    let result = n % 11 == 0;
    proof {
        if result {
            // If n % 11 == 0, then 11 divides n
            assert(n as int % 11 == 0);
            let k = n as int / 11;
            assert(11 * k == n as int) by {
                assert(n as int == 11 * (n as int / 11) + n as int % 11);
                assert(n as int % 11 == 0);
            };
        } else {
            // If n % 11 != 0, then 11 does not divide n
            assert(n as int % 11 != 0);
            assert(forall|k: int| #[trigger] (11 * k) != n as int) by {
                // Proof by contradiction
                if exists|k: int| #[trigger] (11 * k) == n as int {
                    let witness_k = choose|k: int| #[trigger] (11 * k) == n as int;
                    assert(11 * witness_k == n as int);
                    assert(n as int % 11 == 0) by {
                        assert(n as int == 11 * witness_k);
                    };
                    assert(false); // Contradiction
                }
            };
        }
    }
    result
}

fn main() {}

}