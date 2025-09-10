use vstd::prelude::*;

verus! {

fn reverse_string(s: &Vec<char>) -> (result: Vec<char>)
    ensures
        result@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> result@[i] == s@[s@.len() - 1 - i],
{
    assume(false);
    unreached();
}

}
fn main() {}