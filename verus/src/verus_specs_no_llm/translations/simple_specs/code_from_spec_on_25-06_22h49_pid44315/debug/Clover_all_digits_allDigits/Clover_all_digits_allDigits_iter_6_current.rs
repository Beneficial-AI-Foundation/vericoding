use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn is_digit(c: char) -> bool {
    c == '0' || c == '1' || c == '2' || c == '3' || c == '4' || 
    c == '5' || c == '6' || c == '7' || c == '8' || c == '9'
}

fn allDigits(s: Seq<char>) -> (result: bool)
    ensures
        result <==> (forall i: int :: 0 <= i < s.len() ==> is_digit(s[i]))
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall j: int :: 0 <= j < i ==> is_digit(s[j as int])
    {
        let c = s[i as int];
        
        if !is_digit(c) {
            return false;
        }
        i = i + 1;
    }
    
    return true;
}

}