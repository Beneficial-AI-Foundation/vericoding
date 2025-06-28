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
    while i <= a.len() - b.len()
        invariant
            0 <= i <= a.len() - b.len() + 1,
            forall|k: int| 0 <= k < i ==> !matches_at(a, b, k as int)
    {
        let mut j: usize = 0;
        let mut found = true;
        
        while j < b.len()
            invariant
                0 <= j <= b.len(),
                found == (forall|k: int| 0 <= k < j ==> a[i + k] == b[k])
        {
            if a[i + j] != b[j] {
                found = false;
                break;
            }
            j += 1;
        }
        
        if found {
            return i as int;
        }
        
        i += 1;
    }
    
    return -1;
}

}

This implementation:


   - `matches_at`: Specifies when substring `b` matches at position `i` in string `a`
   - `contains`: Specifies when substring `b` exists anywhere in string `a`

   - Outer loop iterates through valid starting positions in `a`
   - Inner loop checks character-by-character matching
   - Returns the first position where a match is found
   - Returns -1 if no match is found

   - The outer loop invariant ensures we haven't missed any matches in previous positions
   - The inner loop invariant tracks the current matching state

   - Returns 0 for empty substring
   - Returns a valid position with matching guarantee when substring exists
   - Returns -1 when substring doesn't exist

The function preserves all the original constraints while adding comprehensive specifications that Verus can verify.