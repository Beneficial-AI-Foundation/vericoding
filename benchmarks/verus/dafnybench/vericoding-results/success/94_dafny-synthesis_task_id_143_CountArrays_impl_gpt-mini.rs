use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn count_arrays(arrays: &Vec<Vec<i32>>) -> (count: usize)
    ensures 
        count >= 0,
        count == arrays.len(),
// </vc-spec>
// <vc-code>
{
    arrays.len()
}
// </vc-code>

fn main() {
}

}