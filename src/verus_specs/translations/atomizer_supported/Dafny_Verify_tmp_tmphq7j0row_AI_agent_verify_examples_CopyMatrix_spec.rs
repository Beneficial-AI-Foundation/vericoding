pub fn CopyMatrix(src: &mut [Vec<i32>], dst: &mut [Vec<i32>])
    requires
        src.len() == dst.len(),
        forall|i: usize| i < src.len() ==> src[i].len() == dst[i].len(),
    ensures
        forall|i: usize, j: usize| 0 <= i < src.len() && 0 <= j < src[i].len() ==> dst[i][j] == old(src)[i][j]
{
}