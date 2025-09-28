use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn array_product(a: &[i32], b: &[i32]) -> (c: Vec<i32>)
    requires 
        a.len() == b.len(),
    ensures 
        c.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] * b[i] == c[i],
// </vc-spec>
// <vc-code>
{
    let mut c: Vec<i32> = Vec::new();
    let n = a.len();

    // Preserve the length of the vector 'c' throughout the loop
    // and demonstrate that elements of 'c' are correctly computed
    // based on 'a' and 'b'.
    #[invariant(
        // i is within the bounds of the array lengths
        0 <= i_native as int <= n as int,
        // The length of 'c' corresponds to the number of elements processed
        c.len() as int == i_native as int,
        // For all elements already processed, their value in 'c' is the product of 'a' and 'b'
        forall|j: int| 0 <= j < i_native as int ==> a[j] * b[j] == c.view_at(j),
    )]
    let mut i_native: usize = 0;
    while i_native < n
    {
        c.push(a[i_native] * b[i_native]);
        i_native = i_native + 1;
    }
    c
}
// </vc-code>

fn main() {}

}