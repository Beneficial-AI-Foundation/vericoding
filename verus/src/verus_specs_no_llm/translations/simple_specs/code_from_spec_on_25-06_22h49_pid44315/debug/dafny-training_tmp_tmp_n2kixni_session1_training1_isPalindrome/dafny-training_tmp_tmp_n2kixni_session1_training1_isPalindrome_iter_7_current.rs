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
        assert(forall|j: int| 0 <= j < len ==> a[j] == a[len - 1 - j]) by {
            assert(forall|j: int| 0 <= j < len ==> {
                let mirror = len - 1 - j;
                if j < half_len {
                    // j is in first half, we checked this pair directly
                    a[j] == a[mirror]
                } else if j >= len - half_len {
                    // j is in second half, mirror is in first half
                    // We checked the pair (mirror, j) in the loop
                    let symmetric_idx = mirror;
                    symmetric_idx < half_len && a[symmetric_idx] == a[len - 1 - symmetric_idx]
                } else {
                    // j is a middle element (only possible for odd length)
                    j == mirror && a[j] == a[mirror]
                }
            });
        }
    }
    
    true
}

}