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
        
        // When left >= right and left + right == s.len() - 1:
        // If left > right: left >= right + 1, so 2*left >= left + right + 1 = s.len()
        // If left == right: 2*left = left + right = s.len() - 1, so 2*left + 1 = s.len()
        assert(2 * left >= s.len() - 1) by {
            if left > right {
                assert(left >= right + 1);
                assert(2 * left >= left + right + 1);
                assert(2 * left >= s.len() - 1 + 1);
                assert(2 * left >= s.len());
            } else {
                assert(left == right);
                assert(2 * left == left + right);
                assert(2 * left == s.len() - 1);
            }
        };
        
        // Show that we've checked all necessary indices
        assert(forall i: int :: 0 <= i < s.len() / 2 ==> i < left) by {
            assert(forall i: int :: 0 <= i < s.len() / 2 ==> {
                &&& 2 * i < s.len()
                &&& 2 * i <= s.len() - 1
                &&& 2 * left >= s.len() - 1
                &&& 2 * i <= 2 * left
                &&& i <= left
            });
            
            // We need to show strict inequality i < left
            assert(forall i: int :: 0 <= i < s.len() / 2 ==> i != left) by {
                assert(forall i: int :: 0 <= i < s.len() / 2 && i == left ==> {
                    &&& 2 * i < s.len()
                    &&& i == left
                    &&& 2 * left < s.len()
                    &&& 2 * left >= s.len() - 1
                    &&& s.len() - 1 <= 2 * left < s.len()
                    &&& 2 * left == s.len() - 1  // only possibility
                    &&& 2 * i == s.len() - 1
                    &&& 2 * i + 1 == s.len()
                    &&& 2 * i < 2 * i + 1  // true
                    &&& 2 * i < s.len()    // true
                    &&& i < s.len() / 2    // given
                });
                // But s.len() / 2 * 2 <= s.len(), and if s.len() = 2*i + 1, then s.len()/2 = i
                // So i < s.len()/2 = i is impossible
                assert(forall i: int :: 0 <= i < s.len() / 2 && i == left ==> false) by {
                    assert(forall i: int :: 0 <= i < s.len() / 2 && i == left ==> {
                        &&& 2 * i < s.len()
                        &&& s.len() / 2 <= i  // since 2 * i + 1 = s.len() implies s.len() / 2 = i when s.len() is odd
                        &&& i < s.len() / 2   // given
                        &&& false
                    });
                };
            };
        };
        
        // Therefore the postcondition holds
        assert(forall i: int :: 0 <= i < s.len() / 2 ==> s.spec_index(i) == s.spec_index(s.len() - 1 - i));
    }
    
    return true;
}

}