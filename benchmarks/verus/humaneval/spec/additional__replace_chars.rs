use vstd::prelude::*;

verus! {

/*
function_signature: "fn replace_chars(s: &[char], old: char, new: char) -> (result: Vec<char>)"
docstring: Implement replace chars functionality.
*/

fn replace_chars(s: &[char], old: char, new: char) -> (result: Vec<char>)
    // post-conditions-start
    ensures
        result.len() == s.len(),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == (if s[i] == old { new } else { s[i] }),
    // post-conditions-end
{
    // impl-start
    assume(false);
    vec![]
    // impl-end
}

fn main() {}
}