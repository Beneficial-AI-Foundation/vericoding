use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers as the issue was a compilation error due to unclosed delimiters in the overall file structure.
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn split_array(arr: &[i32], l: usize) -> (Vec<i32>, Vec<i32>)
    requires 0 <= l <= arr.len()
{
// </vc-spec>
// </vc-spec>

// <vc-code>
fn split_array(arr: &[i32], l: usize) -> (Vec<i32>, Vec<i32>)
    requires 0 <= l <= arr.len()
    ensures |result: (Vec<i32>, Vec<i32>)| {
        result.0.len() == l &&
        result.1.len() == arr.len() - l &&
        forall |i: usize| 0 <= i < l ==> result.0@[i] == arr@[i] &&
        forall |i: usize| 0 <= i < arr.len() - l ==> result.1@[i] == arr@[l + i]
    }
{
    let mut left = Vec::new();
    let mut right = Vec::new();
    
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            left.len() == if i < l { i } else { l },
            right.len() == if i < l { 0 } else { i - l },
            forall |j: usize| 0 <= j < left.len() ==> left@[j] == arr@[j],
            forall |j: usize| 0 <= j < right.len() ==> right@[j] == arr@[l + j]
    {
        if i < l {
            left.push(arr@[i]);
        } else {
            right.push(arr@[i]);
        }
        i = i + 1;
    }
    
    (left, right)
}
// </vc-code>

fn main() {
}

}