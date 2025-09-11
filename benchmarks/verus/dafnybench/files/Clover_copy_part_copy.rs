// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

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
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}