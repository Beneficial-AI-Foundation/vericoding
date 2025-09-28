// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn merge(v1: Vec<i8>, v2: Vec<i8>) -> (result: Vec<i8>)
    requires
        forall|i: int, j: int| 0 <= i < j < v1.len() ==> v1[i] <= v1[j],
        forall|i: int, j: int| 0 <= i < j < v2.len() ==> v2[i] <= v2[j],
    ensures
        result.len() == v1.len() + v2.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        result@.to_multiset() == v1@.to_multiset().add(v2@.to_multiset()),
{
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;

    while i < v1.len() || j < v2.len()
        invariant
            0 <= i <= v1.len(),
            0 <= j <= v2.len(),
            result.len() == i + j,
            result@.to_multiset() == v1@.subrange(0, i as int).to_multiset().add(v2@.subrange(0, j as int).to_multiset()),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] <= result[l],
            forall|k_res: int, k1: int| 0 <= k_res < result.len() && i <= k1 < v1.len() ==> result[k_res] <= v1[k1],
            forall|k_res: int, k2: int| 0 <= k_res < result.len() && j <= k2 < v2.len() ==> result[k_res] <= v2[k2],
        decreases (v1.len() - i) + (v2.len() - j)
    {
        if i < v1.len() && (j >= v2.len() || v1[i] <= v2[j]) {
            result.push(v1[i]);
            i = i + 1;
        } else {
            result.push(v2[j]);
            j = j + 1;
        }
    }
    result
}

/* helper modified by LLM (iteration 4): fixed compilation errors in loop invariants */
fn sub_vec(v: &Vec<i8>, from: usize, to: usize) -> (result: Vec<i8>)
    requires
        from <= to <= v.len(),
    ensures
        result.len() == to - from,
        result@ == v@.subrange(from as int, to as int),
{
    let mut i = from;
    let mut res = Vec::new();
    while i < to
        invariant
            from <= i <= to,
            res.len() == i - from,
            res@ == v@.subrange(from as int, i as int),
        decreases to - i
    {
        res.push(v[i]);
        i = i + 1;
    }
    res
}

/* helper modified by LLM (iteration 3): added recursive msort helper with decreases clause */
fn msort_recursive(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] as int <= result[j] as int,
        result@.to_multiset() =~= a@.to_multiset(),
    decreases a.len()
{
    if a.len() <= 1 {
        a
    } else {
        let mid = a.len() / 2;
        let left = sub_vec(&a, 0, mid);
        let right = sub_vec(&a, mid, a.len());

        let sorted_left = msort_recursive(left);
        let sorted_right = msort_recursive(right);

        merge(sorted_left, sorted_right)
    }
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
    /* code modified by LLM (iteration 4): implemented by calling a recursive helper */
    msort_recursive(a)
}
// </vc-code>

}
fn main() {}