// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn is_sorted_on_seq(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> (#[trigger] s.index(i)) <= s.index(j)
}

/* helper modified by LLM (iteration 4): fixed multiset addition to use add method */
fn merge(left: Vec<i32>, right: Vec<i32>) -> (result: Vec<i32>) 
    requires is_sorted_vec(left), is_sorted_vec(right)
    ensures is_sorted_vec(result),
            result.len() == left.len() + right.len(),
            result@.to_multiset() == left@.to_multiset().add(right@.to_multiset())
{
    let mut result = Vec::new();
    let mut i = 0;
    let mut j = 0;
    while i < left.len() && j < right.len()
        invariant i <= left.len(), j <= right.len(),
                 result.len() == i + j,
    {
        if left[i] <= right[j] {
            result.push(left[i]);
            i += 1;
        } else {
            result.push(right[j]);
            j += 1;
        }
    }
    while i < left.len() {
        result.push(left[i]);
        i += 1;
    }
    while j < right.len() {
        result.push(right[j]);
        j += 1;
    }
    result
}

/* helper modified by LLM (iteration 4): used index method for Seq indexing */

/* helper modified by LLM (iteration 5): added is_sorted_vec to support merge */
fn is_sorted_vec(vec: Vec<i32>) -> bool {
    is_sorted_on_seq(vec@)
}
// </vc-helpers>

// <vc-spec>
fn msort(a: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        result@.to_multiset() =~= a@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by replacing range slicing with manual vector creation using loops */
    if a.len() <= 1 {
        a
    } else {
        let mid = a.len() / 2;
        let mut left = Vec::new();
        for i in 0..mid {
            left.push(a[i]);
        }
        let mut right = Vec::new();
        for i in mid..a.len() {
            right.push(a[i]);
        }
        let sorted_left = msort(left);
        let sorted_right = msort(right);
        merge(sorted_left, sorted_right)
    }
}
// </vc-code>

}
fn main() {}