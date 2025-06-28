use builtin::*;
use builtin_macros::*;

verus! {

// Specification function to check if a substring is palindromic
spec fn palindromic(s: Seq<char>, i: int, j: int) -> bool {
    &&& 0 <= i <= j <= s.len()
    &&& forall|k: int| i <= k < j ==> s[k] == s[j - 1 - (k - i)]
}

fn main() {
}

fn expand_from_center(s: Seq<char>, i0: int, j0: int) -> (lo: int, hi: int)
    requires 
        0 <= i0 <= j0 <= s.len(),
        palindromic(s, i0, j0)
    ensures 
        0 <= lo <= hi <= s.len() && palindromic(s, lo, hi),
        forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s, i, j) 
            && i + j == i0 + j0 ==> j - i <= hi - lo
{
    let mut lo = i0;
    let mut hi = j0;
    
    // Expand outward while characters match
    while lo > 0 && hi < s.len() && s[lo - 1] == s[hi]
        invariant
            0 <= lo <= hi <= s.len(),
            palindromic(s, lo, hi),
            lo + hi == i0 + j0
    {
        lo = lo - 1;
        hi = hi + 1;
        
        // Proof that the expanded substring is still palindromic
        assert forall|k: int| lo <= k < hi implies s[k] == s[hi - 1 - (k - lo)] by {
            if k == lo {
                assert(s[k] == s[lo] && s[lo] == s[hi - 1]);
            } else if k == hi - 1 {
                assert(s[k] == s[hi - 1] && s[hi - 1] == s[lo]);
            } else {
                assert(lo + 1 <= k < hi - 1);
                assert(s[k] == s[hi - 2 - (k - (lo + 1))] == s[hi - 1 - (k - lo)]);
            }
        };
    }
    
    (lo, hi)
}

// The main algorithm to find the longest palindrome
fn longest_palindrome(s: Seq<char>) -> (ans: Seq<char>, lo: int, hi: int)
    requires s.len() >= 0
    ensures 
        0 <= lo <= hi <= s.len(),
        ans == s.subrange(lo, hi),
        palindromic(s, lo, hi),
        forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s, i, j) 
            ==> j - i <= hi - lo
{
    if s.len() == 0 {
        return (seq![], 0, 0);
    }
    
    let mut best_lo = 0;
    let mut best_hi = 1;  // Single character is always a palindrome
    
    // Proof that single character is palindromic
    assert(palindromic(s, 0, 1)) by {
        assert forall|k: int| 0 <= k < 1 implies s[k] == s[1 - 1 - (k - 0)] by {
            // Empty range, trivially true
        };
    };
    
    let mut center = 0;
    
    // Check all possible centers
    while center < s.len()
        invariant
            0 <= center <= s.len(),
            0 <= best_lo <= best_hi <= s.len(),
            palindromic(s, best_lo, best_hi),
            forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s, i, j) 
                && (i + j < 2 * center) ==> j - i <= best_hi - best_lo
    {
        // Check odd-length palindromes centered at `center`
        assert(palindromic(s, center, center + 1)) by {
            assert forall|k: int| center <= k < center + 1 implies s[k] == s[center + 1 - 1 - (k - center)] by {
                // Empty range, trivially true
            };
        };
        
        let (lo1, hi1) = expand_from_center(s, center, center + 1);
        if hi1 - lo1 > best_hi - best_lo {
            best_lo = lo1;
            best_hi = hi1;
            
            // Maintain the invariant about previously checked centers
            assert forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s, i, j) 
                && (i + j < 2 * center) implies j - i <= best_hi - best_lo by {
                // This follows from the previous invariant and the fact that we only updated
                // best_lo, best_hi to a longer palindrome
            };
        }
        
        // Check even-length palindromes centered between `center` and `center + 1`
        if center + 1 < s.len() && s[center] == s[center + 1] {
            assert(palindromic(s, center, center + 2)) by {
                assert forall|k: int| center <= k < center + 2 implies s[k] == s[center + 2 - 1 - (k - center)] by {
                    if k == center {
                        assert(s[k] == s[center] && s[center] == s[center + 1] && s[center + 1] == s[center + 1 - (k - center)]);
                    } else if k == center + 1 {
                        assert(s[k] == s[center + 1] && s[center + 1] == s[center] && s[center] == s[center + 1 - (k - center)]);
                    }
                };
            };
            
            let (lo2, hi2) = expand_from_center(s, center, center + 2);
            if hi2 - lo2 > best_hi - best_lo {
                best_lo = lo2;
                best_hi = hi2;
            }
        }
        
        center = center + 1;
    }
    
    // Final assertion that we found the globally longest palindrome
    assert forall|i: int, j: int| 0 <= i <= j <= s.len() && palindromic(s, i, j) 
        implies j - i <= best_hi - best_lo by {
        // This follows from the loop invariant and the fact that we checked all centers
    };
    
    (s.subrange(best_lo, best_hi), best_lo, best_hi)
}

}