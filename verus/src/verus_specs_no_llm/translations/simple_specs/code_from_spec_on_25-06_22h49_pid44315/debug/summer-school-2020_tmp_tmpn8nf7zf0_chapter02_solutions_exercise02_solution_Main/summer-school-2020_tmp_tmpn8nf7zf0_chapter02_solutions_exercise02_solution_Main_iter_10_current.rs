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
    
    // We need to prove that for all f with 1 < f < 3, !divides(f, 3)
    // The only such f is f = 2
    assert(forall|f: nat| (1 < f && f < 3) ==> f == 2);
    
    // Now prove that 2 does not divide 3
    assert(!divides(2, 3)) by {
        // We need to show that there's no k such that 3 == 2 * k
        assert(forall|k: nat| 3 != 2 * k) by {
            // Case analysis on possible values of k
            assert(2 * 0 == 0 && 0 != 3);
            assert(2 * 1 == 2 && 2 != 3);
            assert(forall|k: nat| k >= 2 ==> 2 * k >= 4);
            assert(4 > 3);
            // Therefore no k satisfies 3 == 2 * k
        }
        // Since no k exists such that 3 == 2 * k, divides(2, 3) is false
    }
    
    // Combine the results
    assert(forall|f: nat| (1 < f && f < 3) ==> !divides(f, 3)) by {
        // The only f with 1 < f < 3 is f = 2, and we proved !divides(2, 3)
    }
    
    // Therefore IsPrime(3) holds
    assert(IsPrime(3)) by {
        assert(1 < 3);
        assert(forall|f: nat| (1 < f && f < 3) ==> !divides(f, 3));
    }
}

}