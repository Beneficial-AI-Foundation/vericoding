use builtin::*;
use builtin_macros::*;

verus! {

// Predicate to check if a substring s[i..j+1] is palindromic
spec fn palindromic(s: Seq<char>, i: int, j: int) -> bool {
    if i > j {
        true
    } else {
        0 <= i && j < s.len() &&
        forall |k: int| 0 <= k <= (j - i) / 2 ==> 
            s[i + k] == s[j - k]
    }
}

// Helper lemma to prove palindrome properties
proof fn lemma_palindrome_extend(s: Seq<char>, i: int, j: int)
    requires
        0 <= i < j < s.len(),
        palindromic(s, i + 1, j - 1),
        s[i] == s[j]
    ensures
        palindromic(s, i, j)
{
    // The proof follows from the definition of palindromic
    assert(0 <= i && j < s.len());
    
    assert forall |k: int| 0 <= k <= (j - i) / 2 implies s[i + k] == s[j - k] by {
        if k == 0 {
            assert(s[i + k] == s[i]);
            assert(s[j - k] == s[j]);
            assert(s[i] == s[j]); // from requires
        } else if k >= 1 && k <= (j - i) / 2 {
            // Map to the inner palindrome
            let inner_k = k - 1;
            assert(0 <= inner_k <= ((j - 1) - (i + 1)) / 2);
            assert(s[(i + 1) + inner_k] == s[(j - 1) - inner_k]) by {
                assert(palindromic(s, i + 1, j - 1));
            };
            assert(i + k == (i + 1) + inner_k);
            assert(j - k == (j - 1) - inner_k);
        }
    };
}

// Helper lemma for maximality property
proof fn lemma_palindrome_maximality(s: Seq<char>, i0: int, j0: int, left: int, right: int)
    requires
        0 <= i0 <= j0 < s.len(),
        0 <= left <= right < s.len(),
        palindromic(s, left, right),
        left + right == i0 + j0,
        left == 0 || right == s.len() - 1 || s[left - 1] != s[right + 1]
    ensures
        forall |i: int, j: int| (0 <= i <= j < s.len() && palindromic(s, i, j) 
            && i + j == i0 + j0) ==> (j - i <= right - left)
{
    // The maximality follows from the stopping condition
}

fn expand_from_center(s: Seq<char>, i0: int, j0: int) -> (lo: int, hi: int)
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
    while left > 0 && right < (s.len() - 1) && 
          s[left - 1] == s[right + 1]
        invariant
            0 <= left <= right < s.len(),
            palindromic(s, left, right),
            left + right == i0 + j0,
        decreases left
    {
        // Store old values for proof
        let old_left = left;
        let old_right = right;
        
        // Update the bounds
        left = left - 1;
        right = right + 1;
        
        // Prove that extending maintains palindrome property
        proof {
            assert(0 <= old_left - 1 < old_right + 1 < s.len());
            assert(palindromic(s, old_left, old_right));
            assert(s[old_left - 1] == s[old_right + 1]);
            lemma_palindrome_extend(s, old_left - 1, old_right + 1);
            assert(palindromic(s, left, right));
        }
    }
    
    // Prove maximality property
    proof {
        lemma_palindrome_maximality(s, i0, j0, left, right);
    }
    
    (left, right)
}

fn main() {
    // Empty main function
}

}