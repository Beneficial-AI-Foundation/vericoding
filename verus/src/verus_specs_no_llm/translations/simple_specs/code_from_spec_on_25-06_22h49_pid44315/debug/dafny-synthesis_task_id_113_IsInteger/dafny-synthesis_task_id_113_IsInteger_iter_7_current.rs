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
            forall|j: int| 0 <= j < i ==> IsDigit(s[j]),
            s.len() > 0
    {
        if !is_digit_exec(s[i as int]) {
            assert(exists|k: int| 0 <= k < s.len() && !IsDigit(s[k]));
            return false;
        }
        i = i + 1;
    }
    
    assert(i == s.len());
    assert(forall|j: int| 0 <= j < s.len() ==> IsDigit(s[j]));
    true
}

}