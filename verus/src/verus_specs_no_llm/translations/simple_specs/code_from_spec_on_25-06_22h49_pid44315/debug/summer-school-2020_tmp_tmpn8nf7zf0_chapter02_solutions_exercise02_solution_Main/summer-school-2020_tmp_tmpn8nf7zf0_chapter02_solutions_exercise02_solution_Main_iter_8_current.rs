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
    
    // First establish that the only value f with 1 < f < 3 is f = 2
    assert(forall|f: nat| (1 < f && f < 3) ==> f == 2) by {
        assert(forall|f: nat| (1 < f && f < 3) ==> (f >= 2 && f <= 2));
    }
    
    // Now prove that 2 does not divide 3
    assert(!divides(2, 3)) by {
        // We need to show that there's no k such that 3 == 2 * k
        assert(forall|k: nat| 3 != 2 * k) by {
            // Case analysis on k
            assert(forall|k: nat| 
                if k == 0 { 2 * k == 0 }
                else if k == 1 { 2 * k == 2 }
                else { 2 * k >= 4 }
            );
            // Since 3 is not 0, 2, or >= 4, no k works
            assert(3 != 0);
            assert(3 != 2);
            assert(3 < 4);
        }
    }
    
    // Now we can conclude the main result
    assert(forall|f: nat| (1 < f && f < 3) ==> !divides(f, 3)) by {
        // Since the only such f is 2, and we proved !divides(2, 3)
        assert(forall|f: nat| (1 < f && f < 3) ==> f == 2);
        assert(!divides(2, 3));
    }
    
    // Therefore IsPrime(3) holds
    assert(IsPrime(3));
}

}