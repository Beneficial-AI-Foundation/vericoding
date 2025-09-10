use vstd::prelude::*;

verus! {

spec fn is_alphanumeric_char(c: char) -> bool;

spec fn all_chars_alphanumeric(s: Seq<char>) -> bool
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        is_alphanumeric_char(s[0]) && all_chars_alphanumeric(s.skip(1))
    }
}

fn isalnum(a: Vec<String>) -> (result: Vec<bool>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            result[i] == (a[i]@.len() > 0 && all_chars_alphanumeric(a[i]@))
{
    assume(false);
    unreached()
}

}
fn main() {}