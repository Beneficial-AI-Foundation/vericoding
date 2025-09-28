use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier(external_body)]
#[allow(unused_mut)]
#[allow(unused_variables)]
// No `total_external_body!` macro is needed here. 
// The `external_body` attribute already tells Verus to trust the Rust implementation.
fn vec_len<T>(v: &Vec<T>) -> usize {
    v.len()
}
// </vc-helpers>

// <vc-spec>
fn count_arrays(arrays: &Vec<Vec<i32>>) -> (count: usize)
    ensures 
        count >= 0,
        count == arrays.len(),
// </vc-spec>
// <vc-code>
{
    let count: usize = arrays.len();
    assert(count == arrays.len()); // This assertion is trivially true given the previous line.
    count
}
// </vc-code>

fn main() {
}

}