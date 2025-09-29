use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn smallest_missing_number(s: Seq<int>) -> int
    recommends
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
{
// </vc-spec>
// <vc-code>
{
0
}
// </vc-code>

}

fn main() {}

}