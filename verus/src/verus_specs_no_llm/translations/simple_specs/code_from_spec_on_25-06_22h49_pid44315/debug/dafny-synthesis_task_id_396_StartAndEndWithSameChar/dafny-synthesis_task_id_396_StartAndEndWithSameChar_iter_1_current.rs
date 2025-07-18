use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn StartAndEndWithSameChar(s: String) -> (result: bool)
    requires
        s.len() > 0
    ensures
        result <==> s.spec_index(0) == s.spec_index(s.len() - 1)
{
    let first_char = s.spec_index(0);
    let last_char = s.spec_index(s.len() - 1);
    return first_char == last_char;
}

}