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
            0 <= right < s.len(),
            left + right == s.len() - 1,
            forall i: int :: 0 <= i < left ==> s.spec_index(i) == s.spec_index(s.len() - 1 - i)
    {
        if s[left] != s[right] {
            proof {
                assert(s.spec_index(left as int) != s.spec_index(right as int));
                assert(right as int == s.len() - 1 - (left as int));
                assert(s.spec_index(left as int) != s.spec_index(s.len() - 1 - (left as int)));
                assert(left < s.len() / 2) by {
                    // Since left < right and left + right == s.len() - 1
                    // we have 2 * left < s.len() - 1, so left < (s.len() - 1) / 2
                    // which implies left < s.len() / 2
                    assert(left < right);
                    assert(left + right == s.len() - 1);
                    assert(2 * left < s.len() - 1);
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
        
        // Key insight: when left >= right and left + right == s.len() - 1,
        // we have left >= (s.len() - 1) / 2
        // This means left >= s.len() / 2 (by integer division properties)
        assert(2 * left >= s.len() - 1) by {
            assert(left >= right);
            assert(left + right == s.len() - 1);
        };
        
        // Show that left covers all indices we need to check
        assert(forall i: int :: 0 <= i < s.len() / 2 ==> i < left) by {
            // If i < s.len() / 2, then 2 * i < s.len()
            // Since 2 * left >= s.len() - 1, we have 2 * left >= 2 * i
            // Therefore left > i (since if left == i, then 2*left == 2*i < s.len() <= 2*left + 1,
            // but we know 2*left >= s.len() - 1)
            assert(forall i: int :: 0 <= i < s.len() / 2 ==> {
                &&& 2 * i < s.len()
                &&& 2 * left >= s.len() - 1
                &&& i < left
            });
        };
        
        // Therefore the postcondition holds
        assert(forall i: int :: 0 <= i < s.len() / 2 ==> s.spec_index(i) == s.spec_index(s.len() - 1 - i));
    }
    
    return true;
}

}