// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn find_missing(l: Seq<nat>, curr: nat) -> nat
    requires
        forall|i: int, j: int| 0 <= i < j < l.len() ==> l[i] < l[j],
    decreases l.len(),
    ensures
        forall|k: nat| k < curr ==> l.contains(k),
        !l.contains(result),
        forall|k: nat| k < result ==> l.contains(k),
        result >= curr,
{
    if l.len() == 0 {
        curr
    } else if l[0] == curr {
        find_missing(l.drop(1), curr + 1)
    } else {
        curr
    }
}
// </vc-helpers>

// <vc-spec>
fn smallest_missing(l: Seq<nat>) -> (result: nat)
    requires forall|i: int, j: int| 0 <= i < j < l.len() ==> l[i] < l[j],
    ensures
        !l.contains(result),
        forall|candidate: nat| candidate < result ==> l.contains(candidate)
// </vc-spec>
// <vc-code>
{
    find_missing(l, 0)
}
// </vc-code>

}
fn main() {}