use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsDigit(c: char) -> bool {
    48 <= c as int && c as int <= 57
}

fn is_digit_exec(c: char) -> (result: bool)
    ensures result == IsDigit(c)
{
    let code = c as u32;
    48 <= code && code <= 57
}

fn IsInteger(s: Seq<char>) -> (result: bool)
    ensures
        result <==> (s.len() > 0) && (forall|i: int| 0 <= i < s.len() ==> IsDigit(s[i]))
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
            return false;
        }
        i = i + 1;
    }
    
    assert(i == s.len());
    assert(forall|j: int| 0 <= j < s.len() ==> IsDigit(s[j]));
    true
}

}