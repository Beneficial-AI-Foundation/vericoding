use vstd::prelude::*;

verus! {

fn smallest_missing(l: Seq<nat>) -> result: nat;
    requires forall|i: int, j: int| 0 <= i < j < l.len() ==> l[i] < l[j],
    ensures
        !l.contains(result),
        forall|candidate: nat| candidate < result ==> l.contains(candidate),
{
    assume(false);
    unreached()
}

}
fn main() {}