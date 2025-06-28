use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn divides(f: nat, i: nat) -> bool
    requires 1 <= f
{
    exists|k: nat| i == f * k
}

spec fn IsPrime(i: nat) -> bool {
    && 1 < i
    && (forall|f: nat| (1 < f && f < i) ==> !divides(f, i))
}

// Helper lemma to demonstrate the specs work correctly
proof fn lemma_prime_not_divisible_by_two()
    ensures IsPrime(3)
{
    assert(1 < 3);
    assert(forall|f: nat| (1 < f && f < 3) ==> f == 2);
    assert(forall|f: nat| (1 < f && f < 3) ==> !divides(f, 3)) by {
        assert(forall|k: nat| 3 != 2 * k) by {
            assert(forall|k: nat| k == 0 || k >= 1);
            assert(forall|k: nat| k == 0 ==> 2 * k == 0);
            assert(forall|k: nat| k == 1 ==> 2 * k == 2);
            assert(forall|k: nat| k >= 2 ==> 2 * k >= 4);
            assert(forall|k: nat| 2 * k == 0 || 2 * k == 2 || 2 * k >= 4);
            assert(3 != 0 && 3 != 2 && 3 < 4);
        }
        assert(!divides(2, 3)) by {
            assert(!(exists|k: nat| 3 == 2 * k)) by {
                assert(forall|k: nat| 3 != 2 * k);
            }
        }
    }
}

}