use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsOdd(n: int) -> bool {
    n % 2 == 1
}

fn IsOddAtIndexOdd(a: Vec<int>) -> (result: bool)
    ensures
        result <==> forall |i: int| 0 <= i < a.len() ==> (IsOdd(i) ==> IsOdd(a.spec_index(i)))
{
    let mut i: usize = 1; // Start with the first odd index
    
    while i < a.len()
        invariant
            i % 2 == 1, // i is always odd
            i >= 1,     // i starts at 1 and increases by 2
            forall |j: int| 0 <= j < i ==> (IsOdd(j) ==> IsOdd(a.spec_index(j))),
        decreases a.len() - i,
    {
        if !IsOdd(a[i] as int) {
            return false;
        }
        
        // Prove that i + 2 is still odd before the increment
        assert((i + 2) % 2 == 1) by {
            // Since i % 2 == 1, we have i = 2k + 1 for some integer k
            // Therefore i + 2 = 2k + 1 + 2 = 2k + 3 = 2(k + 1) + 1
            // So (i + 2) % 2 == 1
            assert(i % 2 == 1);
        };
        
        i += 2; // Move to next odd index
    }
    
    // At this point, i >= a.len() and i % 2 == 1 (from loop invariant)
    // We need to prove that all odd indices j with 0 <= j < a.len() satisfy j < i
    assert(forall |j: int| 0 <= j < a.len() && IsOdd(j) ==> j < i) by {
        // Since i >= a.len() and both i and j are odd integers,
        // and j < a.len(), we have j < a.len() <= i
        // But we need to be more careful since i might equal a.len()
        assert(forall |j: int| 0 <= j < a.len() && IsOdd(j) ==> {
            if i == a.len() {
                // If i equals a.len(), then j < a.len() = i, so j < i
                j < i
            } else {
                // If i > a.len(), then j < a.len() < i, so j < i  
                j < i
            }
        });
    };
    
    // Now we can conclude the postcondition holds
    assert(forall |j: int| 0 <= j < a.len() ==> (IsOdd(j) ==> IsOdd(a.spec_index(j)))) by {
        assert(forall |j: int| 0 <= j < a.len() && IsOdd(j) ==> {
            // j < i by the above assertion
            // The loop invariant gives us the property for all indices < i
            assert(j < i);
            assert(IsOdd(a.spec_index(j)));
            true
        });
    };
    
    true
}

}