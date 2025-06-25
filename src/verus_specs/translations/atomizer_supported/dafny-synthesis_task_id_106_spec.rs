pub fn append_array_to_seq(s: Seq<int>, a: &[int]) -> (r: Seq<int>)
    requires(
        true
    )
    ensures(
        |result| == |s| + a.len() &&
        forall|i: int| 0 <= i < |s| ==> result[i] == s[i] &&
        forall|i: int| 0 <= i < a.len() ==> result[|s| + i] == a[i]
    )
{
}