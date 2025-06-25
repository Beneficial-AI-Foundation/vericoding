// ATOM 
spec fn positive(s: Seq<int>) -> bool
{
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

// SPEC 

pub fn mfirstNegative(v: &[int]) -> (b: bool, i: int)
    ensures(b <==> exists|k: int| 0 <= k < v.len() && v[k] < 0)
    ensures(b ==> 0 <= i < v.len() && v[i] < 0 && positive(v.subrange(0, i as int)))
{
}