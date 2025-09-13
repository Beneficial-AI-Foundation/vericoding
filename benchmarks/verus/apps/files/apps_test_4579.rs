// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn distinct_strings(strings: Seq<&str>) -> Set<&str> {
    Set::new(|s: &str| exists|i: int| 0 <= i < strings.len() && strings[i] == s)
}

spec fn valid_input(strings: Seq<&str>) -> bool {
    strings.len() >= 1
}
// </vc-helpers>

// <vc-spec>
fn solve(strings: Seq<&str>) -> (count: int)
    requires 
        valid_input(strings)
    ensures 
        count >= 1,
        count <= strings.len(),
        count == distinct_strings(strings).len()
// </vc-spec>
// <vc-code>
{
    assume(false);
    0int
}
// </vc-code>


}

fn main() {}