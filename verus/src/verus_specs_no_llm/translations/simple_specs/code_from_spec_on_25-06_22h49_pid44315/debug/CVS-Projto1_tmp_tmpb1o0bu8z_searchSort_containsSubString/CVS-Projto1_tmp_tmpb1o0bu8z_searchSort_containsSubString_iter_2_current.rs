use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper function to check if substring b matches at position i in string a
spec fn matches_at(a: Vec<char>, b: Vec<char>, i: int) -> bool {
    &&& 0 <= i <= a.len() - b.len()
    &&& forall|j: int| 0 <= j < b.len() ==> a[i + j] == b[j]
}

// Helper function to check if substring b exists anywhere in string a
spec fn contains(a: Vec<char>, b: Vec<char>) -> bool {
    exists|i: int| 0 <= i <= a.len() - b.len() && matches_at(a, b, i)
}

fn containsSubString(a: Vec<char>, b: Vec<char>) -> (pos: int)
    requires
        0 <= b.len() <= a.len()
    ensures
        if b.len() == 0 {
            pos == 0
        } else if contains(a, b) {
            0 <= pos <= a.len() - b.len() && matches_at(a, b, pos)
        } else {
            pos == -1
        }
{
    if b.len() == 0 {
        return 0;
    }
    
    let mut i: usize = 0;
    while i + b.len() <= a.len()
        invariant
            0 <= i <= a.len() - b.len() + 1,
            forall|k: int| 0 <= k < i ==> !matches_at(a, b, k)
    {
        let mut j: usize = 0;
        let mut found = true;
        
        while j < b.len()
            invariant
                0 <= j <= b.len(),
                found == (forall|k: int| 0 <= k < j ==> a[i as int + k] == b[k]),
                i + b.len() <= a.len()
        {
            if a[i + j] != b[j] {
                found = false;
                break;
            }
            j += 1;
        }
        
        if found {
            // Prove that we found a match at position i
            assert(forall|k: int| 0 <= k < b.len() ==> a[i as int + k] == b[k]);
            assert(matches_at(a, b, i as int));
            return i as int;
        }
        
        // Prove that position i doesn't match
        assert(!matches_at(a, b, i as int));
        i += 1;
    }
    
    // Prove that no position matches
    assert(forall|k: int| 0 <= k <= a.len() - b.len() ==> !matches_at(a, b, k));
    assert(!contains(a, b));
    return -1;
}

}