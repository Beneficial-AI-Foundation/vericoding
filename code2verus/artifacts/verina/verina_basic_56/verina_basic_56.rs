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
    let ghost orig_r = r@;
    let mut i = 0;
    while i < len
        invariant
            i <= len,
            r.len() >= d_start + len,
            src.len() >= s_start + len,
            forall|j: int| 0 <= j < i ==> #[trigger] r[d_start as int + j] == #[trigger] src[s_start as int + j],
            forall|j: int| 0 <= j < d_start ==> #[trigger] r[j] == #[trigger] orig_r[j],
            forall|j: int| d_start as int + len as int <= j < r.len() ==> #[trigger] r[j] == #[trigger] orig_r[j],
            r.len() == orig_r.len(),
        decreases len - i,
    {
        r.set(d_start + i, src[s_start + i]);
        i += 1;
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
    if len == 0 {
        dest.clone()
    } else {
        let r = dest.clone();
        update_segment(r, src, s_start, d_start, len)
    }
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