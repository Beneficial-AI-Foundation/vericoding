// ATOM 
spec fn positive(s: Seq<int>) -> bool
{
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

//ATOM_PLACEHOLDER_mpositive

// SPEC 

pub fn mpositive3(v: &[int]) -> (b: bool)
    ensures(b == positive(v.view(0..v.len() as int)))
{
}

//ATOM_PLACEHOLDER_mpositive4

//ATOM_PLACEHOLDER_mpositivertl