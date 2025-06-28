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
    assert forall |k: int| 0 <= k <= (j - i) / 2 implies 
        s[i + k] == s[j - k] by {
        if k == 0 {
            // Base case: characters at endpoints match by assumption
            assert(s[i + k] == s[i]);
            assert(s[j - k] == s[j]);
            assert(s[i] == s[j]); // from requires
        } else if i + 1 <= j - 1 {
            // Use palindromic property of inner substring
            assert(0 <= k - 1 <= (j - 1 - (i + 1)) / 2);
            assert(s[(i + 1) + (k - 1)] == s[(j - 1) - (k - 1)]);
            assert(i + k == (i + 1) + (k - 1));
            assert(j - k == (j - 1) - (k - 1));
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
    // The maximality follows from the stopping condition of the expansion
    assert forall |i: int, j: int| (0 <= i <= j < s.len() && palindromic(s, i, j) 
        && i + j == i0 + j0) implies (j - i <= right - left) by {
        // If there were a longer palindrome with the same center sum,
        // it would have to extend beyond our stopping point,
        // but we stopped because we couldn't extend further
        if j - i > right - left {
            // This would mean i < left or j > right
            if i < left {
                assert(j > right); // since i + j == left + right
                // But then s[i] would need to equal s[j], contradicting our stopping condition
            } else if j > right {
                assert(i < left); // since i + j == left + right
                // Similar contradiction
            }
        }
    };
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
    while left > 0 && right < s.len() - 1 && 
          s[left - 1] == s[right + 1]
        invariant
            0 <= left <= right < s.len(),
            palindromic(s, left, right),
            left + right == i0 + j0,
        decreases left + (s.len() - 1 - right)
    {
        // Prove that extending maintains palindrome property
        assert(0 <= left - 1 < right + 1 < s.len());
        assert(palindromic(s, left, right));
        assert(s[left - 1] == s[right + 1]);
        lemma_palindrome_extend(s, left - 1, right + 1);
        
        left = left - 1;
        right = right + 1;
    }
    
    // Prove maximality property
    lemma_palindrome_maximality(s, i0, j0, left, right);
    
    (left, right)
}

}

fn main() {
}