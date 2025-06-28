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
    assert(forall|f: nat| (1 < f && f < 3) ==> f == 2) by {
        // Any f with 1 < f < 3 must satisfy f >= 2 and f <= 2, so f == 2
        assert(forall|f: nat| (1 < f && f < 3) ==> (f >= 2 && f < 3));
        assert(forall|f: nat| (f >= 2 && f < 3) ==> f == 2) by {
            // Since f is a natural number, f >= 2 and f < 3 implies f == 2
            assert(forall|f: nat| f >= 2 ==> (f == 2 || f >= 3));
        }
    }
    
    // Now prove that 2 does not divide 3
    assert(!divides(2, 3)) by {
        // Assume for contradiction that divides(2, 3)
        // Then there exists k such that 3 == 2 * k
        // We'll show no such k exists
        
        // For k = 0: 2 * 0 = 0 ≠ 3
        assert(2 * 0 == 0);
        assert(0 != 3);
        
        // For k = 1: 2 * 1 = 2 ≠ 3  
        assert(2 * 1 == 2);
        assert(2 != 3);
        
        // For k >= 2: 2 * k >= 4 > 3
        assert(forall|k: nat| k >= 2 ==> 2 * k >= 4) by {
            assert(forall|k: nat| k >= 2 ==> 2 * k >= 2 * 2);
            assert(2 * 2 == 4);
        }
        assert(4 > 3);
        
        // So for any k, we have 3 ≠ 2 * k
        assert(forall|k: nat| 3 != 2 * k) by {
            assert(forall|k: nat| 
                if k == 0 { 
                    3 != 2 * k 
                } else if k == 1 {
                    3 != 2 * k
                } else {
                    2 * k >= 4 && 3 < 4
                }
            );
        }
        
        // Therefore, there's no k such that 3 == 2 * k
        assert(!(exists|k: nat| 3 == 2 * k));
    }
    
    // Combine the results
    assert(forall|f: nat| (1 < f && f < 3) ==> !divides(f, 3)) by {
        assert(forall|f: nat| (1 < f && f < 3) ==> f == 2);
        assert(!divides(2, 3));
    }
    
    // Therefore IsPrime(3) holds
    assert(IsPrime(3));
}

}