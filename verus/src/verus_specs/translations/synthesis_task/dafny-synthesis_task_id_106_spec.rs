pub fn append_array_to_seq(s: Seq<int>, a: &[int]) -> (r: Seq<int>)
    requires(
        true
    )
    ensures(|result: Seq<int>| {
        &&& result.len() == s.len() + a.len()
        &&& forall|i: int| 0 <= i < s.len() ==> result[i] == s[i]
        &&& forall|i: int| 0 <= i < a.len() ==> result[s.len() + i] == a[i]
    })
{
}