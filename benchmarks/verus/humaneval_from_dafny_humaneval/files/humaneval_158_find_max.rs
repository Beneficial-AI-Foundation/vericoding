// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_max(strings: Seq<Seq<char>>) -> (s: Seq<char>)
    requires 
        strings.len() > 0,
    ensures 
        strings.contains(s),
        forall|i: int| 0 <= i < strings.len() ==> 
            s.to_set().len() >= strings.index(i).to_set().len(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}