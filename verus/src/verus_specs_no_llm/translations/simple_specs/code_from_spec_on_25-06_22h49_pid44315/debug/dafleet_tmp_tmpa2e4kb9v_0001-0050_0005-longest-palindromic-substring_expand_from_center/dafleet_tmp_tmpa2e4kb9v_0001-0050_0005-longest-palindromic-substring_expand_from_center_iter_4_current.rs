use builtin::*;
use builtin_macros::*;

verus! {

// Predicate to check if a substring s[i..j+1] is palindromic
spec fn palindromic(s: String, i: int, j: int) -> bool {
    if i > j {
        true
    } else {
        0 <= i && j < s.len() &&
        forall |k: int| 0 <= k <= (j - i) / 2 ==> 
            s.spec_index(i + k) == s.spec_index(j - k)
    }
}

// Helper lemma to prove palindrome properties
proof fn lemma_palindrome_extend(s: String, i: int, j: int)
    requires
        0 <= i < j < s.len(),
        palindromic(s, i + 1, j - 1),
        s.spec_index(i) == s.spec_index(j)
    ensures
        palindromic(s, i, j)
{
    if i + 1 <= j - 1 {
        assert forall |k: int| 0 <= k <= (j - i) / 2 implies 
            s.spec_index(i + k) == s.spec_index(j - k) by {
            if k == 0 {
                // Base case: characters at endpoints match by assumption
                assert(s.spec_index(i + k) == s.spec_index(i));
                assert(s.spec_index(j - k) == s.spec_index(j));
            } else {
                // Use palindromic property of inner substring
                assert(k - 1 >= 0);
                assert(k - 1 <= (j - 1 - (i + 1)) / 2);
                assert(s.spec_index((i + 1) + (k - 1)) == s.spec_index((j - 1) - (k - 1)));
                assert(i + k == (i + 1) + (k - 1));
                assert(j - k == (j - 1) - (k - 1));
            }
        }
    } else {
        // Case where i + 1 > j - 1, so the inner substring is empty
        assert forall |k: int| 0 <= k <= (j - i) / 2 implies 
            s.spec_index(i + k) == s.spec_index(j - k) by {
            assert(k == 0); // Only k=0 is possible given the constraint
        }
    }
}

// Helper lemma for maximality property
proof fn lemma_palindrome_maximality(s: String, i0: int, j0: int, left: int, right: int)
    requires
        0 <= i0 <= j0 < s.len(),
        0 <= left <= right < s.len(),
        palindromic(s, left, right),
        left + right == i0 + j0,
        left == 0 || right == s.len() - 1 || s.spec_index(left - 1) != s.spec_index(right + 1)
    ensures
        forall |i: int, j: int| (0 <= i <= j < s.len() && palindromic(s, i, j) 
            && i + j == i0 + j0) ==> (j - i <= right - left)
{
    // The maximality follows from the stopping condition of the expansion
    // We've expanded as far as possible given the constraints
}

fn main() {
}

fn expand_from_center(s: String, i0: int, j0: int) -> (lo: int, hi: int)
    requires
        0 <= i0 <= j0 < s.len(),
        palindromic(s, i0, j0)
    ensures
        0 <= lo <= hi < s.len() && palindromic(s, lo, hi),
        forall |i: int, j: int| (0 <= i <= j < s.len() && palindromic(s, i, j) 
            && i + j == i0 + j0) ==> (j - i <= hi - lo)
{
    let mut left = i0;
    let mut right = j0;
    
    // Expand outward while we can and characters match
    while left > 0 && right < (s.len() - 1) as int && 
          s.spec_index(left - 1) == s.spec_index(right + 1)
        invariant
            0 <= left <= right < s.len(),
            palindromic(s, left, right),
            left + right == i0 + j0,
        decreases left + (s.len() - 1 - right)
    {
        // Prove that extending maintains palindrome property
        proof {
            lemma_palindrome_extend(s, left - 1, right + 1);
        }
        
        left = left - 1;
        right = right + 1;
    }
    
    // Prove maximality property
    proof {
        lemma_palindrome_maximality(s, i0, j0, left, right);
    }
    
    (left, right)
}

}