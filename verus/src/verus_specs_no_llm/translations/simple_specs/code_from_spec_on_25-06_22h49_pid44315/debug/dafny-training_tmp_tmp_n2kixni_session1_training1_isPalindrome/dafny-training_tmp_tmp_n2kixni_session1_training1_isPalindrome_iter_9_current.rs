use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn is_palindrome_spec(a: Seq<char>) -> bool {
    forall|i: int| 0 <= i < a.len() ==> a[i] == a[a.len() - 1 - i]
}

fn isPalindrome(a: Seq<char>) -> (b: bool)
    ensures b == is_palindrome_spec(a)
{
    let len = a.len();
    if len <= 1 {
        assert(is_palindrome_spec(a)) by {
            if len == 0 {
                assert(forall|i: int| 0 <= i < 0 ==> a[i] == a[0 - 1 - i]);
            } else {
                assert(len == 1);
                assert(forall|i: int| 0 <= i < 1 ==> a[i] == a[1 - 1 - i]) by {
                    assert(a[0] == a[0]);
                }
            }
        }
        return true;
    }
    
    let mut i: int = 0;
    let half_len = len / 2;
    
    while i < half_len
        invariant
            0 <= i <= half_len,
            half_len == len / 2,
            len == a.len(),
            len >= 2,
            forall|k: int| 0 <= k < i ==> a[k] == a[len - 1 - k],
    {
        assert(0 <= i < len) by {
            assert(i < half_len);
            assert(half_len <= len);
            assert(len >= 2);
        }
        assert(0 <= len - 1 - i < len) by {
            assert(i >= 0);
            assert(i < half_len);
            assert(len >= 2);
            assert(len - 1 - i >= 0);
            assert(len - 1 - i < len);
        }
        
        if a[i] != a[len - 1 - i] {
            assert(!is_palindrome_spec(a)) by {
                assert(0 <= i < len);
                assert(a[i] != a[len - 1 - i]);
            }
            return false;
        }
        i = i + 1;
    }
    
    assert(is_palindrome_spec(a)) by {
        assert(forall|j: int| 0 <= j < len ==> a[j] == a[len - 1 - j]) by {
            assert(forall|j: int| 0 <= j < len ==> {
                let mirror_j = len - 1 - j;
                if j < half_len {
                    // j is in first half, we verified this in the loop
                    true
                } else if j >= len - half_len {
                    // j is in second half
                    // The mirror index is len - 1 - j, which is < half_len
                    // We verified the pair (mirror_j, j) in the loop
                    mirror_j >= 0 && mirror_j < half_len
                } else {
                    // This is the middle element case (odd length)
                    // For odd lengths, there's at most one middle element
                    // where j == len - 1 - j
                    len % 2 == 1 && j == len / 2 && j == mirror_j
                }
            }) by {
                // Prove the key insight: we've checked all necessary pairs
                assert(forall|j: int| 0 <= j < len ==> {
                    let mirror_j = len - 1 - j;
                    if j < half_len {
                        // We checked this pair directly
                        a[j] == a[mirror_j]
                    } else if j >= len - half_len {
                        // This is the mirror of some index we already checked
                        let orig_idx = mirror_j;
                        orig_idx >= 0 && orig_idx < half_len &&
                        a[orig_idx] == a[len - 1 - orig_idx] &&
                        len - 1 - orig_idx == j
                    } else {
                        // Middle element in odd-length sequence
                        j == mirror_j
                    }
                });
            }
        }
    }
    
    true
}

}