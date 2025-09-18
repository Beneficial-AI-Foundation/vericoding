// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added decreases clause to msort function */
spec fn is_sorted(v: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j]
}

fn vec_slice(v: &Vec<i32>, start: usize, end: usize) -> (result: Vec<i32>)
    requires
        start <= end <= v.len(),
    ensures
        result.len() == end - start,
        result@ =~= v@.subrange(start as int, end as int),
{
    let mut result = Vec::new();
    let mut i = start;
    while i < end
        invariant
            start <= i <= end,
            result.len() == i - start,
            result@ =~= v@.subrange(start as int, i as int),
        decreases end - i,
    {
        result.push(v[i]);
        i += 1;
    }
    result
}

fn merge(left: Vec<i32>, right: Vec<i32>) -> (result: Vec<i32>)
    requires
        is_sorted(left@),
        is_sorted(right@),
    ensures
        result.len() == left.len() + right.len(),
        is_sorted(result@),
        result@.to_multiset() =~= left@.to_multiset().add(right@.to_multiset()),
{
    let mut result = Vec::new();
    let mut i = 0;
    let mut j = 0;
    
    while i < left.len() || j < right.len()
        invariant
            0 <= i <= left.len(),
            0 <= j <= right.len(),
            result.len() == i + j,
            is_sorted(result@),
            result@.to_multiset() =~= left@.subrange(0, i as int).to_multiset().add(right@.subrange(0, j as int).to_multiset()),
        decreases left.len() + right.len() - i - j,
    {
        if i >= left.len() {
            result.push(right[j]);
            j += 1;
        } else if j >= right.len() {
            result.push(left[i]);
            i += 1;
        } else if left[i] <= right[j] {
            result.push(left[i]);
            i += 1;
        } else {
            result.push(right[j]);
            j += 1;
        }
    }
    result
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
    /* code modified by LLM (iteration 5): fixed decreases clause syntax */
    if a.len() <= 1 {
        return a;
    }
    
    let mid = a.len() / 2;
    let left = vec_slice(&a, 0, mid);
    let right = vec_slice(&a, mid, a.len());
    
    let sorted_left = msort(left);
    let sorted_right = msort(right);
    
    merge(sorted_left, sorted_right)
} by (decreases a.len())
// </vc-code>

}
fn main() {}