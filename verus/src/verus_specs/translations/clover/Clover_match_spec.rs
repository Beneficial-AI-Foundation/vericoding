pub fn Match(s: &str, p: &str) -> (b: bool)
    requires(s.len() == p.len())
    ensures(b <==> forall|n: int| 0 <= n < s.len() ==> s[n] == p[n] || p[n] == '?')
{
}