// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn comparison(a: Seq<char>, b: Seq<char>, i: int) -> bool 
    decreases a.len() - i, b.len() - i
{
    if (0 <= i <= a.len() && 0 <= i <= b.len()) {
        if (i < a.len() && i < b.len()) {
            if a.index(i) < b.index(i) {
                true
            } else if a.index(i) > b.index(i) {
                false
            } else {
                comparison(a, b, i + 1)
            }
        } else {
            if a.len() <= b.len() {
                true
            } else {
                false
            }
        }
    } else {
        false
    }
}
// </vc-preamble>

// <vc-helpers>
spec fn lex_le(a: Seq<char>, b: Seq<char>) -> bool {
    comparison(a, b, 0)
}
// </vc-helpers>

// <vc-spec>
fn sort_strings(list: Vec<Vec<char>>) -> (sorted: Vec<Vec<char>>)
    ensures
        sorted@.len() == list@.len(),
        sorted@.to_multiset() == list@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    list
}
// </vc-code>


}

fn main() {}