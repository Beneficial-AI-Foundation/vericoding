// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): predicate: ascending sortedness over sequences */
spec fn sorted(s: Seq<i32>) -> bool { forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j] }

/* helper modified by LLM (iteration 4): merge two sorted vectors by taking the larger tail element; uses multiset add instead of '+' */
fn merge_sorted(mut a: Vec<i32>, mut b: Vec<i32>) -> (result: Vec<i32>)
    requires
        sorted(a@),
        sorted(b@)
    ensures
        sorted(result@),
        result@.to_multiset() =~= a@.to_multiset().add(b@.to_multiset()),
        result.len() == a.len() + b.len()
    decreases a.len() + b.len()
{
    if a.len() == 0 {
        b
    } else if b.len() == 0 {
        a
    } else {
        let ai = a[a.len() - 1];
        let bi = b[b.len() - 1];
        if ai >= bi {
            a.pop();
            let mut res = merge_sorted(a, b);
            res.push(ai);
            res
        } else {
            b.pop();
            let mut res = merge_sorted(a, b);
            res.push(bi);
            res
        }
    }
}

/* helper modified by LLM (iteration 4): recursive mergesort using split_off for partition and merge_sorted for combine */
fn msort_rec(mut v: Vec<i32>) -> (result: Vec<i32>)
    ensures
        sorted(result@),
        result@.to_multiset() =~= v@.to_multiset(),
        result.len() == v.len()
    decreases v.len()
{
    let n = v.len();
    if n <= 1 {
        return v;
    }
    let mid = n / 2;
    let mut right = v.split_off(mid);
    let left_sorted = msort_rec(v);
    let right_sorted = msort_rec(right);
    let merged = merge_sorted(left_sorted, right_sorted);
    merged
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
    /* code modified by LLM (iteration 4): delegate to verified recursive mergesort */
    let res = msort_rec(a);
    res
}
// </vc-code>

}
fn main() {}