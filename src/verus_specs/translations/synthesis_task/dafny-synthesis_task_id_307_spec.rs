pub fn deep_copy_seq(s: Seq<int>) -> (copy: Seq<int>)
    ensures
        copy.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> copy[i] == s[i],
{
}