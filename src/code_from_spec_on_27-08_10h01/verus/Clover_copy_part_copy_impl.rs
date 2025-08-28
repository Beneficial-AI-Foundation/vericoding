use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn copy_preserves_dest_prefix(dest: Seq<i32>, r: Seq<i32>, d_start: int) -> bool {
    d_start >= 0 && d_start <= dest.len() ==> 
        r.subrange(0, d_start) =~= dest.subrange(0, d_start)
}

spec fn copy_preserves_dest_suffix(dest: Seq<i32>, r: Seq<i32>, d_start: int, len: int) -> bool {
    d_start >= 0 && len >= 0 && d_start + len <= dest.len() ==>
        r.subrange(d_start + len, dest.len() as int) =~= dest.subrange(d_start + len, dest.len() as int)
}

spec fn copy_copies_src_range(src: Seq<i32>, r: Seq<i32>, s_start: int, d_start: int, len: int) -> bool {
    s_start >= 0 && d_start >= 0 && len >= 0 && 
    s_start + len <= src.len() && d_start + len <= r.len() ==>
        r.subrange(d_start, d_start + len) =~= src.subrange(s_start, s_start + len)
}
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
{
    let mut result = Vec::new();
    
    // Copy the entire dest array first
    for i in 0..dest.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == dest@[j],
    {
        result.push(dest[i]);
    }
    
    // Now overwrite the specified range with data from src
    for i in 0..len
        invariant
            result.len() == dest.len(),
            0 <= i <= len,
            d_start + i <= dest.len(),
            s_start + i <= src.len(),
            (d_start + i) as usize < result.len(),
            (s_start + i) as usize < src.len(),
            // Preserve prefix when d_start > 0
            d_start > 0 ==> result@.subrange(0, d_start as int) =~= dest@.subrange(0, d_start as int),
            // Preserve suffix when d_start + len < dest.len()
            d_start + len < dest.len() ==> result@.subrange((d_start + len) as int, dest.len() as int) =~= dest@.subrange((d_start + len) as int, dest.len() as int),
            // Copy progress: elements [d_start, d_start + i) have been copied
            forall|j: int| d_start <= j < d_start + i ==> result@[j] == src@[s_start + (j - d_start)],
            // Unchanged suffix within copy range - use bounds to satisfy indexing
            forall|j: int| d_start + i <= j < d_start + len && 0 <= j < result.len() && 0 <= j < dest.len() ==> result@[j] == dest@[j],
    {
        result.set((d_start + i) as usize, src[(s_start + i) as usize]);
    }
    
    result
}
// </vc-code>

fn main() {
}

}