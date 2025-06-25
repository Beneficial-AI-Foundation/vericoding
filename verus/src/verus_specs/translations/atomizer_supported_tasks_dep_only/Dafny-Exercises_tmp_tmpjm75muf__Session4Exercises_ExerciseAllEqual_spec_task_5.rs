use vstd::prelude::*;

verus! {

spec fn allEqual(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]
}

pub fn mallEqual5(v: &[int]) -> (b: bool)
    ensures
        b == allEqual(v@),
{
}

}