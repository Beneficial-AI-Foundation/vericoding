use vstd::prelude::*;

verus! {

fn count_non_empty_substrings(s: Seq<char>) -> (count: usize)
    ensures 
        count >= 0,
        count == (s.len() * (s.len() + 1)) / 2,
{
    assume(false);
    unreached();
}

}
fn main() {}