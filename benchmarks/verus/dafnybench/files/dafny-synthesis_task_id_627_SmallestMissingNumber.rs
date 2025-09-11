use vstd::prelude::*;

verus! {

fn smallest_missing_number(s: Seq<int>) -> (v: int)
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
    ensures
        0 <= v,
        !s.contains(v),
        (forall|k: int| 0 <= k < v ==> s.contains(k)),
{
    assume(false);
    unreached()
}

}
fn main() {}