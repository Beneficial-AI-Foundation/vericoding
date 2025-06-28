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
            right == s.len() - 1 - left,
            forall i: int :: 0 <= i < left ==> s.spec_index(i) == s.spec_index(s.len() - 1 - i)
    {
        if s[left] != s[right] {
            proof {
                assert(s.spec_index(left as int) != s.spec_index(right as int));
                assert(right as int == s.len() - 1 - (left as int));
                assert(s.spec_index(left as int) != s.spec_index(s.len() - 1 - (left as int)));
                assert(left < s.len() / 2) by {
                    assert(left < right);
                    assert(right == s.len() - 1 - left);
                    assert(left < s.len() - 1 - left);
                    assert(2 * left < s.len() - 1);
                    assert(left < (s.len() - 1) / 2);
                    // Since s.len() >= 2, we have (s.len() - 1) / 2 <= s.len() / 2
                    assert(s.len() >= 2);
                    assert((s.len() - 1) / 2 <= s.len() / 2);
                    assert(left < s.len() / 2);
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
        assert(right == s.len() - 1 - left);
        assert(forall i: int :: 0 <= i < left ==> s.spec_index(i) == s.spec_index(s.len() - 1 - i));
        
        // When left >= right and right == s.len() - 1 - left:
        // left >= s.len() - 1 - left
        // 2 * left >= s.len() - 1
        assert(2 * left >= s.len() - 1) by {
            assert(left >= right);
            assert(right == s.len() - 1 - left);
            assert(left >= s.len() - 1 - left);
        };
        
        // Show that we've checked all necessary indices
        assert(forall i: int :: 0 <= i < s.len() / 2 ==> i < left) by {
            assert(forall i: int :: 0 <= i < s.len() / 2 ==> {
                &&& 2 * i < s.len()
                &&& 2 * i <= s.len() - 1
                &&& 2 * left >= s.len() - 1
                &&& 2 * i <= 2 * left
                &&& i <= left
                &&& (i < left || (i == left && 2 * i <= s.len() - 1 && 2 * left >= s.len() - 1))
            });
            
            // For the case i == left, we need to show i < s.len() / 2 implies i < left
            assert(forall i: int :: 0 <= i < s.len() / 2 && i == left ==> false) by {
                assert(forall i: int :: 0 <= i < s.len() / 2 && i == left ==> {
                    &&& 2 * i < s.len()
                    &&& 2 * left >= s.len() - 1
                    &&& i == left
                    &&& 2 * i < s.len()
                    &&& 2 * i >= s.len() - 1
                    &&& s.len() - 1 <= 2 * i < s.len()
                    &&& false  // contradiction since s.len() - 1 < s.len() but we need strict inequality
                });
            };
        };
        
        // Therefore the postcondition holds
        assert(forall i: int :: 0 <= i < s.len() / 2 ==> s.spec_index(i) == s.spec_index(s.len() - 1 - i));
    }
    
    return true;
}

}