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
            proof {
                // When we return false, we've found an odd index with non-odd value
                assert(!IsOdd(a.spec_index(i as int)));
                assert(IsOdd(i as int));
                assert(0 <= i < a.len());
                // This contradicts the postcondition if result were true
            }
            return false;
        }
        
        i += 2; // Move to next odd index
    }
    
    // At this point, we've checked all odd indices up to i
    // Since i >= a.len(), we've checked all odd indices in the array
    proof {
        assert(i >= a.len());
        assert(forall |j: int| 0 <= j < i ==> (IsOdd(j) ==> IsOdd(a.spec_index(j))));
        
        // Now prove that this covers all odd indices in the array
        assert(forall |j: int| 0 <= j < a.len() ==> (IsOdd(j) ==> IsOdd(a.spec_index(j)))) by {
            // For any j in [0, a.len()), if IsOdd(j), then we need IsOdd(a.spec_index(j))
            // Since i >= a.len(), we have j < a.len() <= i for all j < a.len()
            // So the invariant covers all indices in the array
            assert forall |j: int| 0 <= j < a.len() && IsOdd(j) implies IsOdd(a.spec_index(j)) by {
                assert(j < a.len());
                assert(a.len() <= i);
                assert(j < i);
                assert(IsOdd(j) ==> IsOdd(a.spec_index(j))); // from invariant
            }
        };
    }
    
    true
}

}