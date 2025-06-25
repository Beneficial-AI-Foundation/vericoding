pub fn interleave(s1: Seq<int>, s2: Seq<int>, s3: Seq<int>) -> (r: Seq<int>)
    requires(s1.len() == s2.len() && s2.len() == s3.len())
    ensures(|result: Seq<int>| result.len() == 3 * s1.len())
    ensures(|result: Seq<int>| forall|i: int| 0 <= i < s1.len() ==> result[3*i] == s1[i] && result[3*i + 1] == s2[i] && result[3*i + 2] == s3[i])
{
}