// ATOM 
spec fn allEqual(s: Seq<int>) -> bool
{
    forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]
}

// SPEC 
pub fn mallEqual4(v: &[int]) -> (b: bool)
    ensures(b == allEqual(v@))
{
}