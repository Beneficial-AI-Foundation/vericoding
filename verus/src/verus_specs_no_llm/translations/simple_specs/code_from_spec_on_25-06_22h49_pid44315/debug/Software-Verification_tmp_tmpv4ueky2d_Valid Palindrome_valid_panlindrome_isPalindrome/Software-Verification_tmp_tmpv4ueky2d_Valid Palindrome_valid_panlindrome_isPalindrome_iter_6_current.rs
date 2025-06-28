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
            forall i: int :: 0 <= i < left ==> s.spec_index(i) == s.spec_index(s.len() - 1 - i)
    {
        if s[left] != s[right] {
            proof {
                assert(s.spec_index(left as int) != s.spec_index(right as int));
                assert(right as int == s.len() - 1 - (left as int));
                assert(s.spec_index(left as int) != s.spec_index(s.len() - 1 - (left as int)));
                assert(left < s.len() / 2);
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
        // When the loop exits, we have left >= right
        // Initially right = s.len() - 1 and left = 0
        // In each iteration, left increases by 1 and right decreases by 1
        // So left + right stays close to s.len() - 1
        // When left >= right, we have left >= (s.len() - 1) / 2
        
        // For the postcondition, we need to show that for any i < s.len() / 2,
        // we have i < left (so our invariant applies)
        
        // Since left >= right and initially left + right = s.len() - 1,
        // and in each step left increases by 1 and right decreases by 1,
        // when left >= right, we have left >= s.len() / 2
        
        if s.len() % 2 == 0 {
            // Even length: need to check pairs (0, n-1), (1, n-2), ..., (n/2-1, n/2)
            assert(left >= s.len() / 2);
        } else {
            // Odd length: need to check pairs (0, n-1), (1, n-2), ..., ((n-1)/2-1, (n+1)/2)
            assert(left >= s.len() / 2);
        }
        
        // Now prove the postcondition
        assert(forall i: int :: 0 <= i < s.len() / 2 ==> i < left);
        assert(forall i: int :: 0 <= i < s.len() / 2 ==> s.spec_index(i) == s.spec_index(s.len() - 1 - i));
    }
    
    return true;
}

}