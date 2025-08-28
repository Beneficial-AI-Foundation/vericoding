use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers in this case
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn copy(src: &[i32], s_start: usize, dest: &[i32], d_start: usize, len: usize) -> (r: Vec<i32>)
    requires 
        src.len() >= s_start + len,
        dest.len() >= d_start + len,
    ensures 
        r.len() == dest.len(),
        r@.subrange(0, d_start as int) =~= dest@.subrange(0, d_start as int),
        r@.subrange((d_start + len) as int, dest.len() as int) =~= dest@.subrange((d_start + len) as int, dest.len() as int),
        r@.subrange(d_start as int, (len + d_start) as int) =~= src@.subrange(s_start as int, (len + s_start) as int),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn copy(src: &[i32], s_start: usize, dest: &[i32], d_start: usize, len: usize) -> (r: Vec<i32>)
    requires 
        src.len() >= s_start + len,
        dest.len() >= d_start + len,
    ensures 
        r.len() == dest.len(),
        r@.subrange(0, d_start as int) =~= dest@.subrange(0, d_start as int),
        r@.subrange((d_start + len) as int, dest.len() as int) =~= dest@.subrange((d_start + len) as int, dest.len() as int),
        r@.subrange(d_start as int, (len + d_start) as int) =~= src@.subrange(s_start as int, (len + s_start) as int),
{
    let mut result: Vec<i32> = Vec::with_capacity(dest.len());
    let mut i: usize = 0;
    
    while i < dest.len()
        invariant
            0 <= i <= dest.len(),
            result.len() == i,
            forall |k: int| 0 <= k < i as int ==> {
                if d_start as int <= k < (d_start + len) as int {
                    result@[k] == src@[(s_start as int + (k - d_start as int))]
                } else {
                    result@[k] == dest@[k]
                }
            },
    {
        if d_start <= i && i < d_start + len {
            result.push(src[s_start + (i - d_start)]);
        } else {
            result.push(dest[i]);
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {
}

}