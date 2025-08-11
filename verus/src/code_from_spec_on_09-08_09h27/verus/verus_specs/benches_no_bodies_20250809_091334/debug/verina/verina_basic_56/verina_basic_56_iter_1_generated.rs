use vstd::prelude::*;

verus! {

// Precondition for the copy function
spec fn copy_precond(src: Seq<i32>, s_start: usize, dest: Seq<i32>, d_start: usize, len: usize) -> bool {
    src.len() >= s_start + len &&
    dest.len() >= d_start + len
}

// Helper function to update a segment - iterative version
fn update_segment(mut r: Vec<i32>, src: &Vec<i32>, s_start: usize, d_start: usize, len: usize) -> (result: Vec<i32>)
    requires
        r.len() >= d_start + len,
        src.len() >= s_start + len,
    ensures
        result.len() == r.len(),
        forall|i: int| 0 <= i < len ==> #[trigger] result[d_start as int + i] == #[trigger] src[s_start as int + i],
        forall|i: int| 0 <= i < d_start ==> #[trigger] result[i] == #[trigger] r[i],
        forall|i: int| d_start as int + len as int <= i < result.len() ==> #[trigger] result[i] == #[trigger] r[i],
{
    let mut j: usize = 0;
    while j < len
        invariant
            r.len() >= d_start + len,
            src.len() >= s_start + len,
            j <= len,
            r.len() == old(r).len(),
            forall|i: int| 0 <= i < j ==> #[trigger] r[d_start as int + i] == #[trigger] src[s_start as int + i],
            forall|i: int| 0 <= i < d_start ==> #[trigger] r[i] == #[trigger] old(r)[i],
            forall|i: int| d_start as int + len as int <= i < r.len() ==> #[trigger] r[i] == #[trigger] old(r)[i],
            forall|i: int| d_start as int + j as int <= i < d_start as int + len as int ==> #[trigger] r[i] == #[trigger] old(r)[i],
    {
        r.set(d_start + j, src[s_start + j]);
        j = j + 1;
    }
    r
}

// Main copy function
fn copy(src: &Vec<i32>, s_start: usize, dest: &Vec<i32>, d_start: usize, len: usize) -> (result: Vec<i32>)
    requires
        copy_precond(src@, s_start, dest@, d_start, len),
    ensures
        result.len() == dest.len(),
        forall|i: int| 0 <= i < d_start ==> #[trigger] result[i] == #[trigger] dest[i],
        forall|i: int| d_start as int + len as int <= i < result.len() ==> #[trigger] result[i] == #[trigger] dest[i],
        forall|i: int| 0 <= i < len ==> #[trigger] result[d_start as int + i] == #[trigger] src[s_start as int + i],
{
    let mut result = dest.clone();
    result = update_segment(result, src, s_start, d_start, len);
    result
}

// Postcondition specification
spec fn copy_postcond(
    src: Seq<i32>, 
    s_start: usize, 
    dest: Seq<i32>, 
    d_start: usize, 
    len: usize, 
    result: Seq<i32>
) -> bool {
    result.len() == dest.len() &&
    (forall|i: int| 0 <= i < d_start ==> #[trigger] result[i] == #[trigger] dest[i]) &&
    (forall|i: int| d_start as int + len as int <= i < result.len() ==> #[trigger] result[i] == #[trigger] dest[i]) &&
    (forall|i: int| 0 <= i < len ==> #[trigger] result[d_start as int + i] == #[trigger] src[s_start as int + i])
}

} // verus!

fn main() {}