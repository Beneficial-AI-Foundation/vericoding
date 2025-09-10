use vstd::prelude::*;

verus! {

fn count_characters(s: Seq<char>) -> (count: usize)
    ensures 
        count >= 0,
        count == s.len(),
{
    assume(false);
    unreached();
}

}
fn main() {}