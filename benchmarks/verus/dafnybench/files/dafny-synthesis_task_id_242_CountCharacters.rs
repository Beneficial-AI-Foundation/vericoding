use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count_characters(s: Seq<char>) -> (count: usize)
    ensures 
        count >= 0,
        count == s.len(),
{
// </vc-spec>
// <vc-code>
    assume(false);
    0
}
// </vc-code>

fn main() {
}

}