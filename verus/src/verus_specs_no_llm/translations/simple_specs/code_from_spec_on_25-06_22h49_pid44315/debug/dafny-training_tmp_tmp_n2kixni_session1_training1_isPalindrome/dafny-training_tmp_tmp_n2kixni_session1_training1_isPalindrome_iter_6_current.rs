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
                assert(forall|i: int| 0 <= i < 1 ==> a[i] == a[1 - 1 - i]);
                assert(a[0] == a[0]);
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
            assert(half_len <= len / 2);
            assert(len >= 2);
        }
        assert(0 <= len - 1 - i < len) by {
            assert(i >= 0);
            assert(i < half_len);
            assert(len >= 2);
            assert(len - 1 - i >= len - 1 - half_len);
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
        // We've checked pairs (0, len-1), (1, len-2), ..., (half_len-1, len-half_len)
        assert(forall|k: int| 0 <= k < half_len ==> a[k] == a[len - 1 - k]);
        
        // Now prove for all indices
        assert(forall|j: int| 0 <= j < len ==> a[j] == a[len - 1 - j]) by {
            let half = len / 2;
            
            // For any index j in [0, len)
            assert(forall|j: int| 0 <= j < len ==> {
                let mirror = len - 1 - j;
                // mirror is also in valid range
                0 <= mirror < len &&
                // Either j is in first half (already checked)
                // or j is in second half (symmetric to first half)
                // or j is the middle element (for odd length)
                if j < half {
                    // Direct from loop invariant
                    a[j] == a[mirror]
                } else if j > half {
                    // j is in second half, mirror is in first half
                    // We checked (mirror, j) in the loop
                    mirror < half && a[mirror] == a[j]
                } else {
                    // j == half, so j is middle element
                    // mirror = len - 1 - j = len - 1 - half
                    // For odd len: half = len/2, so mirror = len - 1 - len/2 = half
                    // For even len: this case doesn't occur since j < half or j >= half
                    j == mirror
                }
            });
        }
    }
    
    true
}

}