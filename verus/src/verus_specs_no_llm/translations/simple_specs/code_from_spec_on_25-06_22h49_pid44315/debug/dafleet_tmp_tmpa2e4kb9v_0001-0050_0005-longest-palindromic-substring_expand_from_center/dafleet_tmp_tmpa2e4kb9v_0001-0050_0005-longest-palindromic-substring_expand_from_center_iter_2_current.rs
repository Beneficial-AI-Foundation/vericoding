use builtin::*;
use builtin_macros::*;

verus! {

// Predicate to check if a substring s[i..j+1] is palindromic
spec fn palindromic(s: String, i: int, j: int) -> bool {
    i <= j ==> {
        forall |k: int| 0 <= k <= (j - i) / 2 ==> 
            s.spec_index(i + k) == s.spec_index(j - k)
    }
}

// Helper lemma to prove palindrome properties
proof fn lemma_palindrome_extend(s: String, i: int, j: int)
    requires
        0 <= i < j <= s.len(),
        palindromic(s, i + 1, j - 1),
        s.spec_index(i) == s.spec_index(j)
    ensures
        palindromic(s, i, j)
{
}

// Helper lemma for maximality property
proof fn lemma_palindrome_maximality(s: String, i0: int, j0: int, left: int, right: int)
    requires
        0 <= i0 <= j0 <= s.len(),
        0 <= left <= right <= s.len(),
        palindromic(s, left, right),
        left + right == i0 + j0,
        left > 0 ==> right >= s.len() - 1 || s.spec_index(left - 1) != s.spec_index(right + 1),
        right < s.len() - 1 ==> left <= 0 || s.spec_index(left - 1) != s.spec_index(right + 1)
    ensures
        forall |i: int, j: int| (0 <= i <= j <= s.len() && palindromic(s, i, j) 
            && i + j == i0 + j0) ==> (j - i <= right - left)
{
}

fn main() {
}

fn expand_from_center(s: String, i0: int, j0: int) -> (lo: int, hi: int)
    requires
        0 <= i0 <= j0 <= s.len(),
        palindromic(s, i0, j0)
    ensures
        0 <= lo <= hi <= s.len() && palindromic(s, lo, hi),
        forall |i: int, j: int| (0 <= i <= j <= s.len() && palindromic(s, i, j) 
            && i + j == i0 + j0) ==> (j - i <= hi - lo)
{
    let mut left = i0;
    let mut right = j0;
    
    // Expand outward while we can and characters match
    while left > 0 && right < s.len() - 1 && 
          s.spec_index(left - 1) == s.spec_index(right + 1)
        invariant
            0 <= left <= right <= s.len(),
            palindromic(s, left, right),
            left + right == i0 + j0,
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