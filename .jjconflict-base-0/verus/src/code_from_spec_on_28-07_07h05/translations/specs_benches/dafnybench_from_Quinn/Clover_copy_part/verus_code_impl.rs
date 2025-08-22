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
        let mut i = 0;
        
        /* code modified by LLM (iteration 1): fixed loop invariants to properly maintain subrange properties */
        while i < len
            invariant
                i <= len,
                result.len() == dest.len(),
                d_start + len <= result.len(),
                s_start + len <= src.len(),
                result@.subrange(0, d_start as int) == dest@.subrange(0, d_start as int),
                result@.subrange(d_start as int, (d_start + i) as int) == src@.subrange(s_start as int, (s_start + i) as int),
                result@.subrange((d_start + i) as int, dest.len() as int) == dest@.subrange((d_start + i) as int, dest.len() as int),
            decreases len - i
        {
            /* code modified by LLM (iteration 1): removed ownership transfer issue by eliminating old_result variable */
            assert(s_start + i < src.len());
            assert(d_start + i < result.len());
            
            // Store the old sequence value for reasoning about subrange preservation
            let old_seq = result@;
            result.set(d_start + i, src[s_start + i]);
            
            // Help Verus understand that the subrange properties are preserved
            assert(result@.subrange(0, d_start as int) == old_seq.subrange(0, d_start as int));
            assert(result@.subrange((d_start + i + 1) as int, dest.len() as int) == old_seq.subrange((d_start + i + 1) as int, dest.len() as int));
            
            i += 1;
        }
        
        /* code modified by LLM (iteration 1): added final assertion to help prove postcondition */
        assert(i == len);
        assert(result@.subrange((d_start + len) as int, dest.len() as int) == dest@.subrange((d_start + len) as int, dest.len() as int));
        
        result
    }
}

fn main() {}