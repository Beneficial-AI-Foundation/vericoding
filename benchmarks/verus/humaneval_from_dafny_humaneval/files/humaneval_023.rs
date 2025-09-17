// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(s: Seq<char>) -> bool {
    true
}

spec fn correct_length(s: Seq<char>) -> int {
    s.len() as int
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn strlen(s: Seq<char>) -> int
    recommends valid_input(s)
{
    s.len() as int
}
// </vc-spec>
// <vc-code>
// </vc-code>


}

fn main() {}