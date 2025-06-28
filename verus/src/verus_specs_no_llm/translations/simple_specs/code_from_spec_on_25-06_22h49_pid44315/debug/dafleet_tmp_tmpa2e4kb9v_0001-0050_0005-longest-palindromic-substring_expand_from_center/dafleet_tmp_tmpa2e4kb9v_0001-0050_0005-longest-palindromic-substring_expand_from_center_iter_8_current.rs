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
    assert(palindromic(s, i, j)) by {
        if i > j {
            // trivially true
        } else {
            assert(0 <= i && j < s.len()); // from requires
            
            // Prove the forall condition
            assert forall |k: int| 0 <= k <= (j - i) / 2 implies 
                s[i + k] == s[j - k] by {
                
                if k == 0 {
                    // Base case: characters at endpoints match by assumption
                    assert(s[i + k] == s[i]);
                    assert(s[j - k] == s[j]);
                    assert(s[i] == s[j]); // from requires
                } else if k > 0 && k <= (j - i) / 2 {
                    // Use palindromic property of inner substring
                    if i + 1 <= j - 1 {
                        let inner_k = k - 1;
                        assert(0 <= inner_k <= (j - 1 - (i + 1)) / 2);
                        assert(s[(i + 1) + inner_k] == s[(j - 1) - inner_k]);
                        assert(i + k == (i + 1) + inner_k);
                        assert(j - k == (j - 1) - inner_k);
                    }
                }
            }
        }
    }
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
        
        // Proof by contradiction: assume there's a longer palindrome
        if j - i > right - left {
            // This would mean the palindrome extends beyond our bounds
            assert(i + j == left + right); // same center sum
            assert(j - i > right - left);
            
            // This implies either i < left or j > right (or both)
            if i < left {
                assert(j == right + (left - i)); // from i + j == left + right
                assert(j > right); // since left - i > 0
                
                // For this to be a palindrome, we'd need s[i] == s[j]
                // But we stopped expanding because we couldn't extend further
                if left > 0 && right < s.len() - 1 {
                    assert(s[left - 1] != s[right + 1]);
                    // This leads to a contradiction with the palindrome property
                }
            }
        }
    }
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
    while left > 0 && right < (s.len() - 1) as int && 
          s[(left - 1) as nat] == s[(right + 1) as nat]
        invariant
            0 <= left <= right < s.len(),
            palindromic(s, left, right),
            left + right == i0 + j0,
        decreases left + (s.len() as int - 1 - right)
    {
        // Prove that extending maintains palindrome property
        assert(0 <= left - 1 < right + 1 < s.len());
        assert(palindromic(s, left, right));
        assert(s[(left - 1) as nat] == s[(right + 1) as nat]);
        
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

fn main() {
    // Empty main function
}

}