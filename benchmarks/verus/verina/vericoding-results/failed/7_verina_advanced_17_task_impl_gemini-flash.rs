// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The earlier attempt to fix `seq_add_one_elem` was not quite right for adding a single element. Refactored `seq_add_one_elem` to use `Seq::singleton` which is the correct way to create a Seq with one element. */
spec fn is_sorted(l: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < l.len() ==> l[i] <= l[j]
}
spec fn is_permutation<A>(s1: Seq<A>, s2: Seq<A>) -> bool {
    s1.to_multiset() == s2.to_multiset()
}
spec fn seq_add_one_elem<A>(elem: A) -> Seq<A> {
    Seq::singleton(elem)
}
// </vc-helpers>

// <vc-spec>
fn insertion_sort(l: Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],

        result@.to_multiset() == l@.to_multiset(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected `seq_add_one_elem` to use `Seq::singleton` which means the call site now needs to be `seq_add_one_elem(val)` instead of `seq_add_one_elem(Seq::empty(), val)`. Also, added missing part to `is_sorted` invariant in the outer loop, and adjusted the inner loop's `is_permutation` invariant to include `result@.subrange(0, j as int) + seq_add_one_elem(val)` in both cases. */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;

    while i < l.len()
        invariant
            is_permutation(result@ + l@.subrange(i as int, l.len() as int), l@),
            is_sorted(result@),
            0 <= i <= l.len()
        decreases l.len() - i
    {
        let val = l[i];
        let mut j = 0;
        while j < result.len() && result[j] < val
            invariant
                is_permutation(result@.subrange(0, j as int) + seq_add_one_elem(val) + result@.subrange(j as int, result.len() as int) + l@.subrange(i as int, l.len() as int), l@),
                is_sorted(result@.subrange(0, j as int) + seq_add_one_elem(val) + result@.subrange(j as int, result.len() as int)),
                0 <= j <= result.len(),
                forall|k: int| 0 <= k < j ==> result[k] < val,
                i <= l.len()
            decreases result.len() - j
        {
            j = j + 1;
        }

        result.insert(j, val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}