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
        i += 2; // Move to next odd index
        
        // Proof that i is still odd after increment
        assert(i % 2 == 1);
    }
    
    // At this point, i >= a.len() and i is odd
    // We need to prove that all odd indices j with 0 <= j < a.len() satisfy j < i
    assert(forall |j: int| 0 <= j < a.len() && IsOdd(j) ==> j < i) by {
        // Since i is odd, i >= a.len(), and we increment by 2 starting from 1,
        // all odd indices less than a.len() must be less than i
        assert(forall |j: int| 0 <= j < a.len() && IsOdd(j) ==> {
            // j is odd and j < a.len() <= i, and since both j and i are odd,
            // if j >= i, then j would be >= a.len(), contradicting j < a.len()
            j < i
        });
    };
    
    // Now we can conclude the postcondition holds
    assert(forall |j: int| 0 <= j < a.len() ==> (IsOdd(j) ==> IsOdd(a.spec_index(j)))) by {
        assert(forall |j: int| 0 <= j < a.len() && IsOdd(j) ==> {
            // j < i by the above assertion
            // The loop invariant gives us the property for all indices < i
            IsOdd(a.spec_index(j))
        });
    };
    
    true
}

}