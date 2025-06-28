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
            i % 2 == 1, // i is always odd when in the loop
            forall |j: int| 0 <= j < i ==> (IsOdd(j) ==> IsOdd(a.spec_index(j))),
        decreases a.len() - i,
    {
        if !IsOdd(a[i] as int) {
            return false;
        }
        i += 2; // Move to next odd index
        
        // Prove that i is still odd after increment
        assert(i % 2 == 1) by {
            // Since old(i) % 2 == 1 and we added 2, new i is still odd
        }
    }
    
    // At this point, we've checked all odd indices up to i
    // and i >= a.len(), so we've checked all odd indices in the array
    assert(forall |j: int| 0 <= j < a.len() ==> (IsOdd(j) ==> IsOdd(a.spec_index(j)))) by {
        // The loop invariant gives us this property up to i,
        // and since i >= a.len(), we have it for the entire array
    }
    
    true
}

}