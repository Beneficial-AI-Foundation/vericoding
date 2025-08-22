use vstd::prelude::*;

verus! {
    fn copy_impl(src: Vec<i32>, s_start: usize, dest: Vec<i32>, d_start: usize, len: usize) -> (r: Vec<i32>)
        requires 
            src.len() >= s_start + len,
            dest.len() >= d_start + len,
        ensures
            r.len() == dest.len(),
            r@.subrange(0, d_start as int) == dest@.subrange(0, d_start as int),
            d_start + len <= dest.len() ==> r@.subrange((d_start + len) as int, dest.len() as int) == dest@.subrange((d_start + len) as int, dest.len() as int),
            r@.subrange(d_start as int, (d_start + len) as int) == src@.subrange(s_start as int, (s_start + len) as int),
    {
        let mut result = dest;
        let mut i: usize = 0;
        
        /* code modified by LLM (iteration 1): added decreases clause for loop termination */
        while i < len
            invariant
                i <= len,
                result.len() == dest.len(),
                result@.subrange(0, d_start as int) == dest@.subrange(0, d_start as int),
                d_start + len <= dest.len() ==> result@.subrange((d_start + len) as int, dest.len() as int) == dest@.subrange((d_start + len) as int, dest.len() as int),
                result@.subrange(d_start as int, (d_start + i) as int) == src@.subrange(s_start as int, (s_start + i) as int),
                result@.subrange((d_start + i) as int, (d_start + len) as int) == dest@.subrange((d_start + i) as int, (d_start + len) as int),
            decreases len - i
        {
            result.set(d_start + i, src[s_start + i]);
            i += 1;
        }
        
        result
    }
}

fn main() {}