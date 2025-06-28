use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn isPalindrome(s: Vec<char>) -> (result: bool)
    requires
        1<= s.len() <= 200000
    ensures
        result <==> (forall i: int :: 0 <= i < s.len() / 2 ==> s.spec_index(i) == s.spec_index(s.len() - 1 - i))
{
    let mut left: usize = 0;
    let mut right: usize = s.len() - 1;
    
    while left < right
        invariant
            0 <= left <= s.len(),
            right < s.len(),
            left <= right + 1,
            left + right + 1 == s.len(),
            forall i: int :: 0 <= i < left ==> s.spec_index(i) == s.spec_index(s.len() - 1 - i)
    {
        if s[left] != s[right] {
            proof {
                assert(s.spec_index(left as int) != s.spec_index(right as int));
                assert(right as int == s.len() - 1 - (left as int));
                assert(s.spec_index(left as int) != s.spec_index(s.len() - 1 - (left as int)));
                assert(0 <= left < s.len() / 2);
                assert(!(forall i: int :: 0 <= i < s.len() / 2 ==> s.spec_index(i) == s.spec_index(s.len() - 1 - i)));
            }
            return false;
        }
        left += 1;
        right -= 1;
    }
    
    proof {
        assert(left >= right);
        assert(forall i: int :: 0 <= i < left ==> s.spec_index(i) == s.spec_index(s.len() - 1 - i));
        
        // Show that left >= s.len() / 2
        if s.len() % 2 == 0 {
            assert(left + right + 1 == s.len());
            assert(left >= right);
            assert(2 * left + 1 >= s.len());
            assert(left >= s.len() / 2);
        } else {
            assert(left + right + 1 == s.len());
            assert(left >= right);
            assert(2 * left >= s.len() - 1);
            assert(left >= s.len() / 2);
        }
        
        assert(forall i: int :: 0 <= i < s.len() / 2 ==> s.spec_index(i) == s.spec_index(s.len() - 1 - i));
    }
    
    return true;
}

}