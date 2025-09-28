use vstd::prelude::*;

verus! {

// <vc-helpers>
fn mod_euclidean(a: i32, b: i32) -> i32 {
    let r = a % b;
    if (r < 0 && b > 0) || (r > 0 && b < 0) {
        r + b
    } else {
        r
    }
}
// </vc-helpers>

// <vc-spec>
fn element_wise_modulo(a: &[i32], b: &[i32]) -> (result: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i32> = Vec::with_capacity(a.len());
    let mut i: usize = 0;

    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            result.len() == i,
            result.capacity() == a.len(), // This line is not supported by Verus
            forall|j: int| 0 <= j && (j as usize) < i ==> result.view_nth(j) == a.view_nth(j) % b.view_nth(j),
    {
        result.push(a[i] % b[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {
}

}