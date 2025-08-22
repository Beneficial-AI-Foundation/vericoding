use vstd::prelude::*;

verus! {

// SPEC
// https://numpy.org/doc/2.2/reference/generated/numpy.remainder.html
// Returns the element-wise remainder of division.

fn remainder(a: Vec<i32>, b: Vec<i32>) -> (ret: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures 
        ret.len() == a.len(),
        forall|i: int| 0 <= i < ret.len() ==> ret[i] == a[i] % b[i],
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

}

fn main() {}