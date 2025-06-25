pub fn exchanger(s: Seq<Bases>, x: nat, y: nat) -> (t: Seq<Bases>)
    requires 0 < s.len() && x < s.len() && y < s.len()
    ensures |t| == |s|
    ensures forall|b: nat| 0 <= b < s.len() && b != x && b != y ==> t[b] == s[b]
    ensures t[x] == s[y] && s[x] == t[y]
    ensures s.to_multiset() == t.to_multiset()
{
}

pub fn tester_exchange()
{
}