use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn isPalindrome(s: Vec<char>) -> (result: bool)
    requires
        1 <= s.len() <= 200000
    ensures
        result <==> (forall i: int :: 0 <= i < s.len() / 2 ==> s.spec_index(i) == s.spec_index(s.len() - 1 - i))
{
    if s.len() == 1 {
        return true;
    }
    
    let mut left: usize = 0;
    let mut right: usize = s.len() - 1;
    
    while left < right
        invariant
            0 <= left <= s.len(),
            0 <= right < s.len(),
            left + right == s.len() - 1,
            forall i: int :: 0 <= i < left ==> s.spec_index(i) == s.spec_index(s.len() - 1 - i)
    {
        if s[left] != s[right] {
            proof {
                assert(s.spec_index(left as int) != s.spec_index(right as int));
                assert((left + right) as int == s.len() - 1);
                assert(right as int == s.len() - 1 - (left as int));
                assert(s.spec_index(left as int) != s.spec_index(s.len() - 1 - (left as int)));
                assert(left < s.len() / 2) by {
                    assert(left < right);
                    assert(left + right == s.len() - 1);
                    assert(left < s.len() - 1 - left);
                    assert(2 * left < s.len() - 1);
                    assert(2 * left + 1 <= s.len());
                };
                assert(!(forall i: int :: 0 <= i < s.len() / 2 ==> s.spec_index(i) == s.spec_index(s.len() - 1 - i)));
            }
            return false;
        }
        
        left += 1;
        right -= 1;
    }
    
    proof {
        assert(left >= right);
        assert(left + right == s.len() - 1);
        assert(forall i: int :: 0 <= i < left ==> s.spec_index(i) == s.spec_index(s.len() - 1 - i));
        
        // Key insight: when left >= right, we have checked all positions up to the middle
        assert(left as int >= s.len() / 2) by {
            if left == right {
                // s.len() is odd, left = right = (s.len() - 1) / 2
                assert(2 * left == s.len() - 1);
                assert(left as int == (s.len() - 1) / 2);
                assert(left as int >= s.len() / 2);
            } else {
                // left > right, so left >= right + 1
                assert(left >= right + 1);
                assert(left + right >= right + 1 + right);
                assert(s.len() - 1 >= 2 * right + 1);
                assert(s.len() >= 2 * right + 2);
                assert(left >= right + 1);
                assert(left + right == s.len() - 1);
                assert(left >= (s.len() - 1 - right));
                assert(left >= (s.len() - 1) / 2);
                assert(left as int >= s.len() / 2);
            }
        };
        
        // Since we checked all i < left and left >= s.len() / 2, 
        // we checked all i in [0, s.len() / 2)
        assert(forall i: int :: 0 <= i < s.len() / 2 ==> i < left) by {
            assert(forall i: int :: 0 <= i < s.len() / 2 ==> i < s.len() / 2 <= left);
        };
        
        // Therefore the postcondition holds
        assert(forall i: int :: 0 <= i < s.len() / 2 ==> s.spec_index(i) == s.spec_index(s.len() - 1 - i));
    }
    
    return true;
}

}