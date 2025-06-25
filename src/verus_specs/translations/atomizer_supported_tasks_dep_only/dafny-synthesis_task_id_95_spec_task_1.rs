pub fn smallest_list_length(s: Seq<Seq<int>>) -> (v: int)
    requires(s.len() > 0)
    ensures(forall|i: int| 0 <= i < s.len() ==> v <= s[i].len())
    ensures(exists|i: int| 0 <= i < s.len() && v == s[i].len())
{
}