use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsDigit(c: char) -> bool {
    '0' <= c && c <= '9'
}

fn is_digit_exec(c: char) -> (result: bool)
    ensures result == IsDigit(c)
{
    '0' <= c && c <= '9'
}

spec fn IsInteger(s: Seq<char>) -> bool {
    (s.len() > 0) && (forall|i: int| 0 <= i < s.len() ==> IsDigit(s[i]))
}

fn is_integer_exec(s: Seq<char>) -> (result: bool)
    ensures result == IsInteger(s)
{
    if s.len() == 0 {
        return false;
    }
    
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s.len() > 0,
            forall|j: int| 0 <= j < i ==> IsDigit(s[j]),
    {
        if !is_digit_exec(s[i as int]) {
            // We found a non-digit character at position i
            // This proves that not all characters in s are digits
            assert(!IsDigit(s[i as int]));
            assert(exists|k: int| 0 <= k < s.len() && !IsDigit(s[k]) by {
                let k = i as int;
                assert(0 <= k < s.len());
                assert(!IsDigit(s[k]));
            });
            assert(!(forall|k: int| 0 <= k < s.len() ==> IsDigit(s[k])));
            assert(!IsInteger(s));
            return false;
        }
        i = i + 1;
    }
    
    // When we exit the loop, i == s.len() and all characters checked are digits
    assert(i == s.len());
    assert(forall|j: int| 0 <= j < s.len() ==> IsDigit(s[j]));
    assert(s.len() > 0);
    assert(IsInteger(s));
    true
}

}