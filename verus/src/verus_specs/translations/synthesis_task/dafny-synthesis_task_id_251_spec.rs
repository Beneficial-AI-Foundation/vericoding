pub fn insert_before_each(s: Seq<String>, x: String) -> (v: Seq<String>)
    ensures(|v| == 2 * |s|)
    ensures(forall|i: int| 0 <= i < |s| ==> v[2*i] == x && v[2*i + 1] == s[i])
{
}