pub fn Exchanger(s: Seq<Bases>, x: nat, y: nat) -> (t: Seq<Bases>)
    requires 
        0 < s.len() && x < s.len() && y < s.len()
    ensures 
        |result|.len() == s.len(),
        forall|b: nat| 0 <= b < s.len() && b != x && b != y ==> result[b] == s[b],
        result[x] == s[y] && s[x] == result[y],
        result.to_multiset() == s.to_multiset()
{
}