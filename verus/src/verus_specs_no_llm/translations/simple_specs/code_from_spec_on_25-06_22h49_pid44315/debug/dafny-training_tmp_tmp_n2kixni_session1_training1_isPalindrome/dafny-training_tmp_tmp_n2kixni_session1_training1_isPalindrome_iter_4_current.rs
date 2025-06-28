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
            assert(half_len <= len);
        }
        assert(0 <= len - 1 - i < len) by {
            assert(i >= 0);
            assert(i < half_len);
            assert(half_len <= len);
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
        assert(forall|k: int| 0 <= k < half_len ==> a[k] == a[len - 1 - k]);
        
        assert(forall|j: int| 0 <= j < len ==> a[j] == a[len - 1 - j]) by {
            assert(forall|j: int| 0 <= j < len ==> {
                if j < half_len {
                    a[j] == a[len - 1 - j]
                } else if j >= len - half_len {
                    let mirror_j = len - 1 - j;
                    &&& 0 <= mirror_j < half_len
                    &&& a[mirror_j] == a[len - 1 - mirror_j]
                    &&& len - 1 - mirror_j == j
                    &&& a[j] == a[len - 1 - j]
                } else {
                    // middle element case for odd length
                    j == len - 1 - j && a[j] == a[len - 1 - j]
                }
            });
        }
    }
    
    true
}

}