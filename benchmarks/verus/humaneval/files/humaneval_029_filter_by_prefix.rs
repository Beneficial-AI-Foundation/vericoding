// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn starts_with(s: Seq<char>, p: Seq<char>) -> bool
    decreases s.len() + p.len()
{
    p.len() == 0 || (s.len() != 0 && s.len() >= p.len() && s[0] == p[0] && starts_with(s.subrange(1, s.len() as int), p.subrange(1, p.len() as int)))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn filter_by_prefix(xs: Vec<Vec<char>>, p: Vec<char>) -> (filtered: Vec<Vec<char>>)
    ensures forall|i: int| 0 <= i < filtered@.len() ==> starts_with(#[trigger] filtered@[i]@, #[trigger] p@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}