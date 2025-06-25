// ATOM 
spec fn positive(s: Seq<int>) -> bool
{
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

// SPEC 
pub fn mpositive(v: &[int]) -> (b: bool)
    ensures(b == positive(v@))
{
}

// SPEC 
pub fn mpositive3(v: &[int]) -> (b: bool)
    ensures(b == positive(v@))
{
}

// SPEC 
pub fn mpositive4(v: &[int]) -> (b: bool)
    ensures(b == positive(v@))
{
}

// SPEC 
pub fn mpositivertl(v: &[int]) -> (b: bool)
    ensures(b == positive(v@))
{
}