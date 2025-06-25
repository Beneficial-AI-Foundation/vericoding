pub fn DoubleArray(src: &[i32], dst: &mut [i32])
    requires(src.len() == dst.len())
    ensures(forall|i: usize| 0 <= i < src.len() ==> dst[i] == 2 * old(src)[i])
{
}