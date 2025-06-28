use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn StartAndEndWithSameChar(s: &str) -> (result: bool)
    requires
        s.len() > 0
    ensures
        result <==> s@.index(0) == s@.index(s@.len() - 1)
{
    let s_seq = s@;
    let len = s_seq.len();
    
    let first_char = s_seq.index(0);
    let last_char = s_seq.index(len - 1);
    
    let result = first_char == last_char;
    
    result
}

}