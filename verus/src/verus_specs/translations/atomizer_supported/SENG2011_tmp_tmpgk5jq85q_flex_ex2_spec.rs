// ATOM 
pub fn maxcheck(s: &[nat], i: int, max: int) -> int
    requires 0 <= i <= s.len()
{
}

// SPEC 
pub fn max(s: &[nat]) -> int
    requires s.len() > 0
    ensures |result: int| forall|x: int| 0 <= x < s.len() ==> result >= s[x]
    ensures |result: int| exists|i: int| 0 <= i < s.len() && result == s[i]
{
}

// SPEC 
pub fn Checker()
{
}