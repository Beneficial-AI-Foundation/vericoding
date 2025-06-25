pub fn copy(src: &[i32], sStart: usize, dest: &[i32], dStart: usize, len: usize) -> Vec<i32>
    requires
        src.len() >= sStart + len,
        dest.len() >= dStart + len,
    ensures |r: Vec<i32>|
        r.len() == dest.len() &&
        r[..dStart] == dest[..dStart] &&
        r[dStart + len..] == dest[dStart + len..] &&
        r[dStart..len + dStart] == src[sStart..len + sStart],
{
    unimplemented!()
}