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
pub fn mpositive(v: &[int]) -> (b: bool)
    ensures(b == positive(v@))
{
}

// SPEC 
pub fn mpositive(v: &[int]) -> (b: bool)
    ensures(b == positive(v@))
{
}

// SPEC 
pub fn mpositive(v: &[int]) -> (b: bool)
    ensures(b == positive(v@))
{
}