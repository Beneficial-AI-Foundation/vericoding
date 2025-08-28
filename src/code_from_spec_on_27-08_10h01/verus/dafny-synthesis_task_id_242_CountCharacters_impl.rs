use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
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
fn count_characters(s: Seq<char>) -> (count: usize)
    ensures 
        count >= 0,
        count == s.len(),
{
    s.len()
}
// </vc-code>

fn main() {
}

}