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
    
    // Check if b is too long to fit in a
    if b.len() > a.len() {
        assert(!contains(a, b)) by {
            assert(forall|i: int| !(0 <= i <= a.len() - b.len() && matches_at(a, b, i))) by {
                assert(forall|i: int| !(0 <= i <= a.len() - b.len())) by {
                    assert(a.len() - b.len() < 0);
                }
            }
        };
        return -1;
    }
    
    let mut i: usize = 0;
    let end_pos = a.len() - b.len();
    
    while i <= end_pos
        invariant
            0 <= i <= end_pos + 1,
            end_pos == a.len() - b.len(),
            forall|k: int| 0 <= k < i ==> !matches_at(a, b, k),
            b.len() > 0,
            b.len() <= a.len(),
            end_pos < a.len()
        decreases end_pos + 1 - i
    {
        let mut j: usize = 0;
        
        // Check if pattern matches starting at position i
        while j < b.len()
            invariant
                0 <= j <= b.len(),
                forall|k: int| 0 <= k < j ==> a[i as int + k] == b[k],
                i <= end_pos,
                i as int + b.len() <= a.len(),
                b.len() > 0
            decreases b.len() - j
        {
            if a[i + j] != b[j] {
                break;
            }
            j += 1;
        }
        
        if j == b.len() {
            // We found a complete match
            assert(forall|k: int| 0 <= k < b.len() ==> a[i as int + k] == b[k]);
            assert(0 <= i as int <= a.len() - b.len());
            assert(matches_at(a, b, i as int));
            assert(contains(a, b)) by {
                assert(0 <= i as int <= a.len() - b.len() && matches_at(a, b, i as int));
            };
            return i as int;
        } else {
            // j < b.len(), so we don't have a complete match at position i
            assert(j < b.len());
            assert(a[i + j] != b[j]);
            assert(!matches_at(a, b, i as int)) by {
                // We found a mismatch at position j, so not all characters match
                assert(!(a[i as int + j as int] == b[j as int]));
                assert(0 <= j as int < b.len());
                assert(!(forall|k: int| 0 <= k < b.len() ==> a[i as int + k] == b[k]));
            };
        }
        
        i += 1;
    }
    
    // When we exit the loop, we've checked all valid positions
    assert(forall|k: int| 0 <= k <= a.len() - b.len() ==> !matches_at(a, b, k)) by {
        assert(forall|k: int| 0 <= k < i ==> !matches_at(a, b, k));
        assert(i > end_pos);
        assert(end_pos == a.len() - b.len());
    };
    
    // Since we checked all positions and none matched, contains is false
    assert(!contains(a, b));
    
    return -1;
}

}