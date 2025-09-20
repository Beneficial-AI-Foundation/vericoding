// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_max(strings: Vec<String>) -> (s: String)
    requires 
        strings.len() > 0,
    ensures 
        exists|i: int| 0 <= i < strings.len() && strings@.index(i) == s@,
        forall|i: int| 0 <= i < strings.len() ==> 
            s@.to_set().len() >= strings@.index(i).to_set().len(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}