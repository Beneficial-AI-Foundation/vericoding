pub fn CopyMatrix(src: &mut [[i32; N]; M], dst: &mut [[i32; N]; M])
    requires 
        src.len() == dst.len(),
        src.len() > 0 ==> src[0].len() == dst[0].len()
    ensures
        forall|i: usize, j: usize| 
            0 <= i < src.len() && 0 <= j < src[0].len() ==> 
            dst[i][j] == old(src)[i][j]
{
}