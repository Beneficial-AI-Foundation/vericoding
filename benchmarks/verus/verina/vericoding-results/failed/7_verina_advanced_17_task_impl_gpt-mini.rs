// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): is_sorted predicate */
spec fn is_sorted(v: Vec<i32>) -> bool { forall|i: int, j: int| 0 <= i < j < v.len() ==> v@[i] <= v@[j] }

/* helper modified by LLM (iteration 2): insert element into a sorted vector while preserving sortedness and multiset */
fn insert_into_sorted(mut s: Vec<i32>, x: i32) -> (result: Vec<i32>)
    requires is_sorted(s)
    ensures is_sorted(result) && result@.to_multiset() == s@.to_multiset().insert(x)
{
    let mut i: usize = 0;
    while i < s.len() && s[i] <= x {
        invariant i <= s.len();
        decreases s.len() - i;
        i += 1;
    }
    s.insert(i, x);
    result = s;
}
// </vc-helpers>

// <vc-spec>
fn insertion_sort(l: Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],

        result@.to_multiset() == l@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): iterative insertion sort using insert_into_sorted with loop invariants */
    let mut result: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < l.len() {
        invariant idx <= l.len();
        invariant is_sorted(result);
        invariant result@.to_multiset() == l@.slice(0, idx).to_multiset();
        decreases l.len() - idx;
        result = insert_into_sorted(result, l[idx]);
        idx += 1;
    }
    result
}
// </vc-code>

}
fn main() {}