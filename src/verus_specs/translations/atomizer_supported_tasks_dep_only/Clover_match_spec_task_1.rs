pub fn Match(s: String, p: String) -> (b: bool)
    requires(s.len() == p.len())
    ensures(b <==> forall|n: int| 0 <= n < s.len() ==> s[n] == p[n] || p[n] == '?')
{
}