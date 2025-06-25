pub fn max(s: &[nat]) -> (a: int)
    requires(s.len() > 0)
    ensures(forall|x: int| 0 <= x < s.len() ==> a >= s[x])
    ensures(exists|i: int| 0 <= i < s.len() && a == s[i])
{
}

pub fn Checker()
{
}