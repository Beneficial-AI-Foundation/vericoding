// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_sorted(v: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j]
}

spec fn multiset_equiv(v1: Seq<i32>, v2: Seq<i32>) -> bool {
    v1 =~= v2
}

/* helper modified by LLM (iteration 2): Added decreases clause to merge function loops */
fn merge(left: Vec<i32>, right: Vec<i32>) -> (result: Vec<i32>)
    requires
        is_sorted(left@),
        is_sorted(right@),
    ensures
        result.len() == left.len() + right.len(),
        is_sorted(result@),
        result@ =~= left@ + right@,
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    
    while i < left.len() && j < right.len()
        invariant
            i <= left.len(),
            j <= right.len(),
            result.len() == i + j,
            is_sorted(result@),
            forall|k: int| 0 <= k < result.len() ==> 
                (exists|l: int| 0 <= l < i ==> result[k] == left[l]) ||
                (exists|r: int| 0 <= r < j ==> result[k] == right[r]),
            i < left.len() && j < right.len() ==> 
                forall|k: int| 0 <= k < result.len() ==> 
                    result[k] <= left[i as int] || result[k] <= right[j as int],
        decreases left.len() + right.len() - i - j
    {
        if left[i] <= right[j] {
            result.push(left[i]);
            i = i + 1;
        } else {
            result.push(right[j]);
            j = j + 1;
        }
    }
    
    while i < left.len()
        invariant
            i <= left.len(),
            j == right.len(),
            result.len() == i + j,
            is_sorted(result@),
        decreases left.len() - i
    {
        result.push(left[i]);
        i = i + 1;
    }
    
    while j < right.len()
        invariant
            i == left.len(),
            j <= right.len(),
            result.len() == i + j,
            is_sorted(result@),
        decreases right.len() - j
    {
        result.push(right[j]);
        j = j + 1;
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
fn merge_sort(list: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == list.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        result@ =~= list@,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clauses to loops */
    if list.len() <= 1 {
        return list;
    }
    
    let mid = list.len() / 2;
    let mut left = Vec::new();
    let mut right = Vec::new();
    
    let mut i: usize = 0;
    while i < mid
        invariant
            i <= mid,
            left.len() == i,
            forall|k: int| 0 <= k < i ==> left[k] == list[k],
        decreases mid - i
    {
        left.push(list[i]);
        i = i + 1;
    }
    
    while i < list.len()
        invariant
            mid <= i <= list.len(),
            right.len() == i - mid,
            forall|k: int| 0 <= k < right.len() ==> right[k] == list[mid + k],
        decreases list.len() - i
    {
        right.push(list[i]);
        i = i + 1;
    }
    
    let sorted_left = merge_sort(left);
    let sorted_right = merge_sort(right);
    let result = merge(sorted_left, sorted_right);
    
    result
}
// </vc-code>

}
fn main() {}