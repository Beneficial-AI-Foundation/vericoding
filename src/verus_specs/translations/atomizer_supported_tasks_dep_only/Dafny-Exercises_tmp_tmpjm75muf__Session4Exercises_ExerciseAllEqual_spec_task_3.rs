use vstd::prelude::*;

verus! {

spec fn allEqual(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]
}

proof fn equivalenceContiguous(s: Seq<int>)
    ensures 
        allEqual(s) ==> (forall|i: int| 0 <= i < s.len() - 1 ==> s[i] == s[i + 1]),
        allEqual(s) <== (forall|i: int| 0 <= i < s.len() - 1 ==> s[i] == s[i + 1])
{
}

pub fn mallEqual3(v: &[int]) -> (b: bool)
    ensures b == allEqual(v@)
{
}

}