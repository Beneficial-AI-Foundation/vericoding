// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn sorted(v: Seq<i8>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j]
}

spec fn partition_spec(v: Seq<i8>, pivot: i8) -> (Seq<i8>, Seq<i8>) {
    let less = v.filter(|x: i8| x < pivot);
    let greater_eq = v.filter(|x: i8| x >= pivot);
    (less, greater_eq)
}

/* helper modified by LLM (iteration 5): Added decreases clause to partition loop */
fn partition(v: &Vec<i8>, pivot: i8) -> (result: (Vec<i8>, Vec<i8>))
    ensures
        result.0@.to_multiset().add(result.1@.to_multiset()) =~= v@.to_multiset(),
        forall|i: int| 0 <= i < result.0.len() ==> result.0[i] < pivot,
        forall|i: int| 0 <= i < result.1.len() ==> result.1[i] >= pivot,
        result.0.len() + result.1.len() == v.len(),
{
    let mut less = Vec::new();
    let mut greater_eq = Vec::new();
    let mut i = 0;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            less@.to_multiset().add(greater_eq@.to_multiset()) =~= v@.subrange(0, i as int).to_multiset(),
            forall|j: int| 0 <= j < less.len() ==> less[j] < pivot,
            forall|j: int| 0 <= j < greater_eq.len() ==> greater_eq[j] >= pivot,
            less.len() + greater_eq.len() == i,
        decreases v.len() - i
    {
        if v[i] < pivot {
            less.push(v[i]);
        } else {
            greater_eq.push(v[i]);
        }
        i = i + 1;
    }
    
    (less, greater_eq)
}

/* helper modified by LLM (iteration 5): Added decreases clause to merge loop */
fn merge(left: Vec<i8>, right: Vec<i8>) -> (result: Vec<i8>)
    requires
        sorted(left@),
        sorted(right@),
    ensures
        result.len() == left.len() + right.len(),
        sorted(result@),
        result@.to_multiset() =~= left@.to_multiset().add(right@.to_multiset()),
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    
    while i < left.len() || j < right.len()
        invariant
            0 <= i <= left.len(),
            0 <= j <= right.len(),
            result.len() == i + j,
            sorted(result@),
            result@.to_multiset() =~= left@.subrange(0, i as int).to_multiset().add(right@.subrange(0, j as int).to_multiset()),
            i < left.len() && result.len() > 0 ==> result[(result.len() - 1) as int] <= left[i as int],
            j < right.len() && result.len() > 0 ==> result[(result.len() - 1) as int] <= right[j as int],
        decreases left.len() + right.len() - i - j
    {
        if i >= left.len() {
            result.push(right[j]);
            j = j + 1;
        } else if j >= right.len() {
            result.push(left[i]);
            i = i + 1;
        } else if left[i] <= right[j] {
            result.push(left[i]);
            i = i + 1;
        } else {
            result.push(right[j]);
            j = j + 1;
        }
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
fn msort(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] as int <= result[j] as int,
        result@.to_multiset() =~= a@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added decreases clause */
    if a.len() <= 1 {
        return a;
    }
    
    let pivot = a[0];
    let (less, greater_eq) = partition(&a, pivot);
    
    if less.len() == 0 {
        let mut sorted_geq = msort(greater_eq);
        return sorted_geq;
    } else if greater_eq.len() == 0 {
        let mut sorted_less = msort(less);
        return sorted_less;
    } else {
        let sorted_less = msort(less);
        let sorted_geq = msort(greater_eq);
        let result = merge(sorted_less, sorted_geq);
        return result;
    }
}
// </vc-code>

}
fn main() {}