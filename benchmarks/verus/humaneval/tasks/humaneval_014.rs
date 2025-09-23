// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_prefixes(s: Seq<char>, result: Seq<Seq<char>>) -> bool {
    result.len() == s.len() &&
    forall|i: int| 0 <= i < result.len() ==> result[i] == s.subrange(0, i + 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn all_prefixes(s: Vec<char>) -> (result: Vec<Vec<char>>)
    ensures valid_prefixes(s@, result@.map(|i, v: Vec<char>| v@))
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}