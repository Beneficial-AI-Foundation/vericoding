use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this specification
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn count_characters(s: Seq<char>) -> (count: usize)
    ensures 
        count >= 0,
        count == s.len(),
{
// </vc-spec>
// </vc-spec>

// <vc-code>
let count = s.len();
count
// </vc-code>

fn main() {
}

}