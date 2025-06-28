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
            forall|k: int| 0 <= k < i ==> !matches_at(a, b, k),
            i + b.len() <= a.len() + 1
    {
        let mut j: usize = 0;
        let mut found = true;
        
        while j < b.len()
            invariant
                0 <= j <= b.len(),
                found == (forall|k: int| 0 <= k < j ==> a[i as int + k] == b[k]),
                i + b.len() <= a.len(),
                i <= a.len() - b.len()
        {
            if a[i + j] != b[j] {
                found = false;
                break;
            }
            j += 1;
        }
        
        if found {
            // When found is true and we've checked all characters, we have a match
            assert(j == b.len());
            assert(forall|k: int| 0 <= k < b.len() ==> a[i as int + k] == b[k]);
            assert(0 <= i <= a.len() - b.len());
            assert(matches_at(a, b, i as int));
            return i as int;
        }
        
        // Prove that matches_at is false for this position
        if !found {
            assert(exists|k: int| 0 <= k < j && a[i as int + k] != b[k]);
            assert(!matches_at(a, b, i as int));
        }
        
        i += 1;
    }
    
    // When we exit the loop, we've checked all valid positions
    assert(i + b.len() > a.len());
    assert(forall|k: int| 0 <= k < i ==> !matches_at(a, b, k));
    
    // Prove that we've checked all valid positions
    if a.len() >= b.len() {
        // Since i + b.len() > a.len() and i + b.len() was <= a.len() + 1 in invariant
        assert(i > a.len() - b.len());
        // All valid positions are in range [0, a.len() - b.len()]
        assert(forall|k: int| 0 <= k <= a.len() - b.len() ==> k < i);
        // We've proven none of the positions we checked match
        assert(forall|k: int| 0 <= k <= a.len() - b.len() ==> !matches_at(a, b, k));
        // Therefore contains is false
        assert(!contains(a, b));
    }
    
    return -1;
}

}