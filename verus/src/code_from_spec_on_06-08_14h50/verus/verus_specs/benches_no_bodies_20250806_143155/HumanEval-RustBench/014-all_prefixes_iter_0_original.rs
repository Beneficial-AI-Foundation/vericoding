use vstd::prelude::*;

verus! {

fn all_prefixes(s: &Vec<u8>) -> (prefixes: Vec<Vec<u8>>)
    // post-conditions-start
    ensures
        prefixes.len() == s.len(),
        forall|i: int| #![auto] 0 <= i < s.len() ==> prefixes[i]@ == s@.subrange(0, i + 1),
    // post-conditions-end
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

}
fn main() {}
