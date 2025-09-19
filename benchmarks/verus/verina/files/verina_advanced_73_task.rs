// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn smallest_missing(l: Seq<nat>) -> nat;
// </vc-spec>
// <vc-code>
proof fn smallest_missing_spec_satisfied(l: Seq<nat>)
    requires forall|i: int, j: int| 0 <= i < j < l.len() ==> l[i] < l[j],
    ensures
        !l.contains(smallest_missing(l)),
        forall|candidate: nat| candidate < smallest_missing(l) ==> l.contains(candidate),
{
    assume(false); // TODO: Remove this line and implement the proof
}
// </vc-code>


}
fn main() {}