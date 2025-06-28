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
            left <= right,
            right < s.len(),
            left + right == s.len() - 1,
            forall i: int :: 0 <= i < left ==> s.spec_index(i) == s.spec_index(s.len() - 1 - i)
    {
        if s[left] != s[right] {
            proof {
                assert(s.spec_index(left as int) != s.spec_index(right as int));
                assert(right as int == s.len() - 1 - (left as int));
                assert(s.spec_index(left as int) != s.spec_index(s.len() - 1 - (left as int)));
                assert(left < right);
                assert(left < s.len() / 2);
                assert(!(forall i: int :: 0 <= i < s.len() / 2 ==> s.spec_index(i) == s.spec_index(s.len() - 1 - i)));
            }
            return false;
        }
        
        proof {
            assert(left + right == s.len() - 1);
            assert(left < right);
            assert(right >= 1); // since left >= 0 and left < right and left + right == s.len() - 1 >= 0
        }
        
        left += 1;
        right -= 1;
    }
    
    proof {
        assert(left >= right);
        assert(left + right == s.len() - 1);
        assert(forall i: int :: 0 <= i < left ==> s.spec_index(i) == s.spec_index(s.len() - 1 - i));
        
        // Show that left >= s.len() / 2
        // Since left >= right and left + right == s.len() - 1
        // We have 2 * left >= left + right == s.len() - 1
        // So left >= (s.len() - 1) / 2
        assert(2 * left >= left + right);
        assert(2 * left >= s.len() - 1);
        assert(left >= (s.len() - 1) / 2);
        
        // For any integer n, (n-1)/2 >= n/2 - 1, and since left is integer, left >= n/2
        if s.len() % 2 == 0 {
            assert((s.len() - 1) / 2 == s.len() / 2 - 1);
            assert(left >= s.len() / 2 - 1);
            assert(left >= s.len() / 2); // since left is integer and >= s.len()/2 - 1
        } else {
            assert((s.len() - 1) / 2 == s.len() / 2);
            assert(left >= s.len() / 2);
        }
        
        // Now prove the postcondition
        assert(forall i: int :: 0 <= i < s.len() / 2 ==> i < left);
        assert(forall i: int :: 0 <= i < s.len() / 2 ==> s.spec_index(i) == s.spec_index(s.len() - 1 - i));
    }
    
    return true;
}

}