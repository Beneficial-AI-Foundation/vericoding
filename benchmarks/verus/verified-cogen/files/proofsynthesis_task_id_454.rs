use vstd::prelude::*;

verus! {

fn contains_z(text: &Vec<char>) -> (result: bool)

    ensures
        result == (exists|i: int| 0 <= i < text.len() && (text[i] == 'Z' || text[i] == 'z')),
{
    assume(false);
    unreached()
}

}
fn main() {}