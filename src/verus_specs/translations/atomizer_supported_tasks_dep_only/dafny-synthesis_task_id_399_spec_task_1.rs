pub fn BitwiseXOR(a: Seq<u32>, b: Seq<u32>) -> (result: Seq<u32>)
    requires(a.len() == b.len())
    ensures(|result: Seq<u32>| result.len() == a.len())
    ensures(|result: Seq<u32>| forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] ^ b[i])
{
}