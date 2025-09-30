use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
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
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    // Copy all elements from dest, but replace the range [d_start, d_start + len) with src elements
    while i < dest.len()
        invariant
            i <= dest.len(),
            result.len() == i,
            src.len() >= s_start + len,  // Add precondition to invariant
            dest.len() >= d_start + len, // Add precondition to invariant
            // Elements before d_start are copied from dest
            forall|j: int| 0 <= j < i && j < d_start as int ==> #[trigger] result@[j] == dest@[j],
            // Elements in the replacement range that have been processed
            forall|j: int| d_start as int <= j < i && j < (d_start + len) as int ==> 
                s_start as int + (j - d_start as int) < src.len() &&
                #[trigger] result@[j] == src@[(s_start as int + (j - d_start as int))],
            // Elements after the replacement range that have been processed
            forall|j: int| (d_start + len) as int <= j < i ==> #[trigger] result@[j] == dest@[j],
        decreases dest.len() - i,
    {
        if i >= d_start && i < d_start + len {
            // We're in the range to copy from src
            let offset = i - d_start;
            assert(offset < len);
            assert(s_start + offset <= s_start + len - 1);
            assert(s_start + len <= src.len()); // From precondition
            assert(s_start + offset < src.len());
            let src_index = s_start + offset;
            result.push(src[src_index]);
        } else {
            // Copy from dest
            result.push(dest[i]);
        }
        i = i + 1;
    }
    
    assert(result.len() == dest.len());
    assert(result@.subrange(0, d_start as int) =~= dest@.subrange(0, d_start as int));
    assert(result@.subrange((d_start + len) as int, dest.len() as int) =~= 
           dest@.subrange((d_start + len) as int, dest.len() as int));
    assert(result@.subrange(d_start as int, (d_start + len) as int) =~= 
           src@.subrange(s_start as int, (s_start + len) as int));
    
    result
}
// </vc-code>

fn main() {
}

}