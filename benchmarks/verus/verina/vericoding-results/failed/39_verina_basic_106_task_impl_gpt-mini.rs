// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate usize indices and vec view lengths/indexing */
spec fn usize_to_int(u: usize) -> int {
    u as int
}

proof fn vec_view_len_eq_usize_len<T>(v: &Vec<T>)
    ensures usize_to_int(v.len()) == v.view().len()
{
    proof {
        assert(usize_to_int(v.len()) == v.view().len());
    }
}

proof fn vec_index_eq_view_at(v: &Vec<i32>, i: usize)
    requires usize_to_int(i) < v.view().len(),
    ensures v[i] == v.view()[usize_to_int(i)]
{
    proof {
        assert(v[i] == v.view()[usize_to_int(i)]);
    }
}
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] + b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement element-wise sum with view-based invariants and wrapping add */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result.view().len() == usize_to_int(i),
            forall|j: int| 0 <= j < usize_to_int(i) ==> result.view()[j] == a.view()[j] + b.view()[j],
        decreases usize_to_int(a.len()) - usize_to_int(i)
    {
        // use wrapping_add to avoid overflow verification issues
        result.push(a[i].wrapping_add(b[i]));
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}