use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn isPalindrome(s: Vec<char>) -> (result: bool)
    requires
        1<= s.len() <= 200000
    ensures
        result <==> (forall i:: 0 <= i < s.len() / 2 ==> s.spec_index(i) == s.spec_index(s.len() - 1 - i))
{
    let mut left = 0;
    let mut right = s.len() - 1;
    
    while left < right
        invariant
            0 <= left <= s.len(),
            0 <= right < s.len(),
            left + right == s.len() - 1,
            forall i:: 0 <= i < left ==> s.spec_index(i) == s.spec_index(s.len() - 1 - i)
    {
        if s[left] != s[right] {
            return false;
        }
        left += 1;
        right -= 1;
    }
    
    return true;
}

}