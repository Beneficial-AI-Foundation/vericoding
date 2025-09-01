use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper function to check if a value exists in the array
proof fn value_exists_in_sorted_array(s: &[i32], v: i32, idx: int)
    requires
        0 <= idx < s.len(),
        s[idx] == v,
    ensures
        exists|j: int| 0 <= j < s.len() && s[j] == v,
{
    assert(s[idx] == v);
}

// Helper lemma: if s[i] > i for some i, then i is not in the array
proof fn gap_means_missing(s: &[i32], i: int)
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
        0 <= i < s.len(),
        s[i] > i,
    ensures
        forall|j: int| 0 <= j < s.len() ==> s[j] != i,
{
    assert forall|j: int| 0 <= j < s.len() implies s[j] != i by {
        if j < i {
            assert(s[j] <= s[i - 1]);
            assert(s[i - 1] < s[i]);
            assert(s[j] < s[i]);
            assert(s[i] > i);
            assert(s[j] < i);
        } else if j == i {
            assert(s[j] == s[i]);
            assert(s[i] > i);
            assert(s[j] > i);
        } else {
            assert(s[j] >= s[i]);
            assert(s[i] > i);
            assert(s[j] > i);
        }
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn smallest_missing_number(s: &[i32]) -> (v: i32)
    // pre-conditions-start
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
        s.len() <= 100_000,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= v,
        forall|i: int| 0 <= i < s.len() ==> s[i] != v,
        forall|k: int| 0 <= k < v && s[k] != v ==> exists|j: int| 0 <= j < s.len() && s[j] == k,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|k: int| 0 <= k < i ==> exists|j: int| 0 <= j < s.len() && s[j] == k,
    {
        if s[i] > i {
            // Found a gap: i is the smallest missing number
            gap_means_missing(s, i as int);
            
            // Verify postconditions
            assert(0 <= i);
            assert(forall|j: int| 0 <= j < s.len() ==> s[j] != i);
            assert(forall|k: int| 0 <= k < i && s[k] != i ==> 
                exists|j: int| 0 <= j < s.len() && s[j] == k);
            
            return i as i32;
        }
        
        // s[i] <= i, and since all values are non-negative and sorted,
        // we know that s[i] must equal some value from 0 to i
        assert(s[i] <= i);
        assert(s[i] >= 0);
        
        // The value i exists at position i (or earlier due to duplicates)
        if s[i] == i {
            value_exists_in_sorted_array(s, i as i32, i as int);
        }
        
        i = i + 1;
    }
    
    // If we've gone through the entire array, the answer is s.len()
    assert(i == s.len());
    assert(forall|k: int| 0 <= k < s.len() ==> 
        exists|j: int| 0 <= j < s.len() && s[j] == k);
    assert(forall|j: int| 0 <= j < s.len() ==> s[j] != s.len());
    
    s.len() as i32
}
// </vc-code>

fn main() {}
}