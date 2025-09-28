// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): changed multiset operator from =~= to == for correct equality check */
spec fn sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

/* helper modified by LLM (iteration 5): changed ensures to use multiset.insert for direct equality check instead of push */
fn insert_into_sorted(vec: Vec<i32>, elem: i32) -> (result: Vec<i32>)
    requires
        sorted(vec@),
    ensures
        sorted(result@),
        result@.to_multiset() == vec@.to_multiset().insert(elem),
{
    let mut v = vec;
    let mut i = 0;
    while i < v.len() && v[i] <= elem
        invariant
            0 <= i <= v.len(),
            forall|k: int| 0 <= k < i ==> v[k] <= elem,
        decreases v.len() - i
    {
        i += 1;
    }
    v.insert(i, elem);
    v
}
// </vc-helpers>

// <vc-spec>
fn insertion_sort(l: Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],

        result@.to_multiset() == l@.to_multiset(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): changed multiset operator from =~= to == in invariant */
/* code modified by LLM (iteration 5): added ensures sorted check in helper to support insertion sort logic */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < l.len()
        invariant
            i <= l.len(),
            result.len() == i,
            sorted(result@),
            result@.to_multiset() == l@.subrange(0, i as int).to_multiset(),
        decreases l.len() - i
    {
        let elem = l[i];
        result = insert_into_sorted(result, elem);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}