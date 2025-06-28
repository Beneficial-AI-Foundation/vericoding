use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsEven(n: int) -> bool {
    n % 2 == 0
}

spec fn IsOdd(n: int) -> bool {
    n % 2 != 0
}

// Helper lemma: every integer is either even or odd
proof fn lemma_even_or_odd(n: int)
    ensures IsEven(n) || IsOdd(n)
{
}

// Helper lemma: no integer is both even and odd
proof fn lemma_not_both_even_and_odd(n: int)
    ensures !(IsEven(n) && IsOdd(n))
{
}

fn FirstEvenOddDifference(a: Vec<int>) -> (diff: int)
    requires
        a.len() >= 2,
        exists i :: 0 <= i < a.len() && IsEven(a.spec_index(i)),
        exists i :: 0 <= i < a.len() && IsOdd(a.spec_index(i))
    ensures
        exists i, j :: 0 <= i < a.len() && 0 <= j < a.len() && 
            IsEven(a.spec_index(i)) && IsOdd(a.spec_index(j)) && 
            diff == a.spec_index(i) - a.spec_index(j) && 
            (forall k :: 0 <= k < i ==> IsOdd(a.spec_index(k))) && 
            (forall k :: 0 <= k < j ==> IsEven(a.spec_index(k)))
{
    let mut first_even_idx: usize = 0;
    let mut first_odd_idx: usize = 0;
    let mut found_even = false;
    let mut found_odd = false;
    
    // Find first even number
    let mut i = 0;
    while i < a.len() && !found_even
        invariant
            0 <= i <= a.len(),
            forall k :: 0 <= k < i ==> IsOdd(a.spec_index(k as int)),
            !found_even
    {
        proof {
            lemma_even_or_odd(a.spec_index(i as int));
        }
        if a[i] % 2 == 0 {
            first_even_idx = i;
            found_even = true;
        } else {
            i += 1;
        }
    }
    
    // Find first odd number  
    let mut j = 0;
    while j < a.len() && !found_odd
        invariant
            0 <= j <= a.len(),
            forall k :: 0 <= k < j ==> IsEven(a.spec_index(k as int)),
            !found_odd
    {
        proof {
            lemma_even_or_odd(a.spec_index(j as int));
        }
        if a[j] % 2 != 0 {
            first_odd_idx = j;
            found_odd = true;
        } else {
            j += 1;
        }
    }
    
    proof {
        // From preconditions, we know even and odd elements exist
        // The loops must have found them since they didn't exhaust without finding
        assert(found_even);
        assert(found_odd);
        assert(first_even_idx < a.len());
        assert(first_odd_idx < a.len());
        
        // Properties of found elements
        assert(IsEven(a.spec_index(first_even_idx as int)));
        assert(IsOdd(a.spec_index(first_odd_idx as int)));
        
        // First property from loop invariants
        assert(forall k :: 0 <= k < first_even_idx ==> IsOdd(a.spec_index(k)));
        assert(forall k :: 0 <= k < first_odd_idx ==> IsEven(a.spec_index(k)));
    }
    
    a[first_even_idx] - a[first_odd_idx]
}

}