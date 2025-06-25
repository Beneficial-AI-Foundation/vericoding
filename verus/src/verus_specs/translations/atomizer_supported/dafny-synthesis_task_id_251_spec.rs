pub fn insert_before_each(s: Seq<String>, x: String) -> (v: Seq<String>)
    ensures(v.len() == 2 * s.len())
    ensures(forall|i: int| 0 <= i < s.len() ==> v[2*i] == x && v[2*i + 1] == s[i])
{
}