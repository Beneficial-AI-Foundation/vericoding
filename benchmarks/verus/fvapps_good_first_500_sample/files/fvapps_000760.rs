// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn minimum(l: Seq<nat>) -> nat 
    decreases l.len()
{
    if l.len() == 0 {
        0
    } else if l.len() == 1 {
        l[0]
    } else {
        if l[0] <= minimum(l.skip(1)) {
            l[0]
        } else {
            minimum(l.skip(1))
        }
    }
}

spec fn maximum(l: Seq<nat>) -> nat 
    decreases l.len()
{
    if l.len() == 0 {
        0
    } else if l.len() == 1 {
        l[0]
    } else {
        if l[0] >= maximum(l.skip(1)) {
            l[0]
        } else {
            maximum(l.skip(1))
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn min_poison_concentration(n: nat, concentrations: Vec<nat>) -> (result: nat)
    requires 
        1 <= n,
        n <= concentrations.len(),
        concentrations.len() > 0,
    ensures
        result >= minimum(concentrations@),
        result <= maximum(concentrations@),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}