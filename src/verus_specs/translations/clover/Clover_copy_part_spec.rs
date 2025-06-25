pub fn copy(src: &[i32], sStart: usize, dest: &[i32], dStart: usize, len: usize) -> Vec<i32>
    requires 
        src.len() >= sStart + len,
        dest.len() >= dStart + len,
    ensures |r: Vec<i32>|
        r.len() == dest.len() &&
        r.subrange(0, dStart as int) == dest.subrange(0, dStart as int) &&
        r.subrange((dStart + len) as int, dest.len() as int) == dest.subrange((dStart + len) as int, dest.len() as int) &&
        r.subrange(dStart as int, (len + dStart) as int) == src.subrange(sStart as int, (len + sStart) as int)
{
}