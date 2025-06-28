use builtin::*;
use builtin_macros::*;

verus! {

// Helper spec function to check if characters are mirrored
spec fn chars_mirror(s: Seq<char>, lo: int, hi: int) -> bool {
    forall|k: int| lo <= k < hi ==> #[trigger] s[k] == s[hi - 1 - (k - lo)]
}

// Refined palindromic definition
spec fn is_palindromic(s: Seq<char>, i: int, j: int) -> bool {
    &&& 0 <= i <= j <= s.len()
    &&& chars_mirror(s, i, j)
}

fn main() {
}

fn expand_from_center(s: Seq<char>, i0: int, j0: int) -> (lo: int, hi: int)
    requires 
        0 <= i0 <= j0 <= s.len(),
        is_palindromic(s, i0, j0)
    ensures 
        0 <= lo <= hi <= s.len() && is_palindromic(s, lo, hi),
        forall|i: int, j: int| 0 <= i <= j <= s.len() && is_palindromic(s, i, j) 
            && i + j == i0 + j0 ==> j - i <= hi - lo
{
    let mut lo = i0;
    let mut hi = j0;
    
    // Expand outward while characters match
    while lo > 0 && hi < s.len() && s[lo - 1] == s[hi]
        invariant
            0 <= lo <= hi <= s.len(),
            is_palindromic(s, lo, hi),
            lo + hi == i0 + j0
    {
        lo = lo - 1;
        hi = hi + 1;
        
        proof {
            // Prove the expanded range is palindromic
            assert(is_palindromic(s, lo, hi)) by {
                assert(forall|k: int| lo <= k < hi ==> s[k] == s[hi - 1 - (k - lo)]) by {
                    if lo < hi {
                        assert(forall|k: int| lo < k < hi - 1 ==> s[k] == s[hi - 1 - (k - lo)]);
                        if lo < hi - 1 {
                            assert(s[lo] == s[hi - 1]);
                        }
                    }
                }
            }
        }
    }
    
    (lo, hi)
}

// The main algorithm to find the longest palindrome
fn longest_palindrome(s: Seq<char>) -> (ans: Seq<char>, lo: int, hi: int)
    requires s.len() >= 0
    ensures 
        0 <= lo <= hi <= s.len(),
        ans == s.subrange(lo, hi),
        is_palindromic(s, lo, hi),
        forall|i: int, j: int| 0 <= i <= j <= s.len() && is_palindromic(s, i, j) 
            ==> j - i <= hi - lo
{
    if s.len() == 0 {
        proof {
            assert(is_palindromic(s, 0, 0)) by {
                assert(chars_mirror(s, 0, 0)) by {
                    assert(forall|k: int| 0 <= k < 0 ==> s[k] == s[0 - 1 - (k - 0)]);
                }
            }
        }
        return (seq![], 0, 0);
    }
    
    let mut best_lo = 0;
    let mut best_hi = 1;  // Single character is always a palindrome
    
    proof {
        assert(is_palindromic(s, 0, 1)) by {
            assert(chars_mirror(s, 0, 1)) by {
                assert(forall|k: int| 0 <= k < 1 ==> s[k] == s[1 - 1 - (k - 0)]) by {
                    assert(forall|k: int| 0 <= k < 1 ==> k == 0);
                    assert(forall|k: int| 0 <= k < 1 ==> s[k] == s[0]);
                }
            }
        }
    }
    
    let mut center = 0;
    
    // Check all possible centers
    while center < s.len()
        invariant
            0 <= center <= s.len(),
            0 <= best_lo <= best_hi <= s.len(),
            is_palindromic(s, best_lo, best_hi),
            forall|i: int, j: int| 0 <= i <= j <= s.len() && is_palindromic(s, i, j) 
                && (i + j < 2 * center) ==> j - i <= best_hi - best_lo
    {
        // Check odd-length palindromes centered at `center`
        proof {
            assert(is_palindromic(s, center, center + 1)) by {
                assert(chars_mirror(s, center, center + 1)) by {
                    assert(forall|k: int| center <= k < center + 1 ==> s[k] == s[center + 1 - 1 - (k - center)]) by {
                        assert(forall|k: int| center <= k < center + 1 ==> k == center);
                        assert(forall|k: int| center <= k < center + 1 ==> s[k] == s[center]);
                    }
                }
            }
        }
        let (lo1, hi1) = expand_from_center(s, center, center + 1);
        if hi1 - lo1 > best_hi - best_lo {
            best_lo = lo1;
            best_hi = hi1;
        }
        
        // Check even-length palindromes centered between `center` and `center + 1`
        if center + 1 < s.len() && s[center] == s[center + 1] {
            proof {
                assert(is_palindromic(s, center, center + 2)) by {
                    assert(chars_mirror(s, center, center + 2)) by {
                        assert(forall|k: int| center <= k < center + 2 ==> s[k] == s[center + 2 - 1 - (k - center)]) by {
                            assert(s[center] == s[center + 1]);
                            assert(forall|k: int| center <= k < center + 2 ==> (k == center || k == center + 1));
                        }
                    }
                }
            }
            let (lo2, hi2) = expand_from_center(s, center, center + 2);
            if hi2 - lo2 > best_hi - best_lo {
                best_lo = lo2;
                best_hi = hi2;
            }
        }
        
        center = center + 1;
    }
    
    (s.subrange(best_lo, best_hi), best_lo, best_hi)
}

}