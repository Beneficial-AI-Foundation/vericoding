use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsDigit(c: char) -> bool {
    48 <= c as int <= 57
}

fn IsInteger(s: String) -> (result: bool)
    ensures
        result <==> (s.len() > 0) && (forall i :: 0 <= i < s.len() ==> IsDigit(s.spec_index(i)))
{
    if s.len() == 0 {
        return false;
    }
    
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall j :: 0 <= j < i ==> IsDigit(s.spec_index(j))
    {
        if !IsDigit(s.spec_index(i)) {
            return false;
        }
        i += 1;
    }
    
    true
}

}