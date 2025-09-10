use vstd::prelude::*;

verus! {

fn split_string_into_chars(s: Vec<char>) -> (v: Vec<char>)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> v[i] == s[i],
{
    assume(false);
    unreached();
}

}
fn main() {}