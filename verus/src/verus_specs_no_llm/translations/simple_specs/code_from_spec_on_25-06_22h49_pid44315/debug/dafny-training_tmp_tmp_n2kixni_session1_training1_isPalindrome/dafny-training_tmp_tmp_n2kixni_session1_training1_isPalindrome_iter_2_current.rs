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
        return true;
    }
    
    let mut i: usize = 0;
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            len == a.len(),
            forall|k: int| 0 <= k < i ==> a[k] == a[len - 1 - k],
    {
        if a[i as int] != a[len - 1 - (i as int)] {
            assert(!is_palindrome_spec(a)) by {
                assert(a[i as int] != a[len - 1 - (i as int)]);
            }
            return false;
        }
        i = i + 1;
    }
    
    assert(is_palindrome_spec(a)) by {
        assert(forall|k: int| 0 <= k < len / 2 ==> a[k] == a[len - 1 - k]);
        assert(forall|k: int| len / 2 <= k < len ==> {
            let mirror_k = len - 1 - k;
            &&& 0 <= mirror_k < len / 2
            &&& a[mirror_k] == a[len - 1 - mirror_k]
            &&& len - 1 - mirror_k == k
            &&& a[k] == a[len - 1 - k]
        });
    }
    
    true
}

}