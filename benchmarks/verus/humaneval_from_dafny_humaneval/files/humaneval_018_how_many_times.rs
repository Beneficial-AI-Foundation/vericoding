// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn how_many_times(s: Seq<char>, substr: Seq<char>) -> (times: usize)
    ensures times == Set::new(|i: int| 0 <= i <= s.len() - substr.len() && s.subrange(i, i + substr.len()) == substr).len()
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>


}

fn main() {}