pub fn copy(src: &[i32], s_start: usize, dest: &[i32], d_start: usize, len: usize) -> Vec<i32>
    requires 
        src.len() >= s_start + len,
        dest.len() >= d_start + len,
    ensures |r: Vec<i32>|
        r.len() == dest.len() &&
        r.subrange(0, d_start as int) == dest.subrange(0, d_start as int) &&
        r.subrange((d_start + len) as int, dest.len() as int) == dest.subrange((d_start + len) as int, dest.len() as int) &&
        r.subrange(d_start as int, (len + d_start) as int) == src.subrange(s_start as int, (len + s_start) as int)
{
}