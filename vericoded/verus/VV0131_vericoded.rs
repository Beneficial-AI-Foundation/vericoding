// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn binary_search_precond(a: &Vec<i32>, key: i32) -> bool {
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Keep a sorted predicate for reasoning */
spec fn is_sorted_vec(a: &Vec<i32>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}
// </vc-helpers>

// <vc-spec>
fn binary_search(a: &Vec<i32>, key: i32) -> (result: usize)
    requires binary_search_precond(a, key),
    ensures
        result <= a.len(),
        forall|i: int| 0 <= i < result ==> a[i] < key,
        forall|i: int| result <= i < a.len() ==> a[i] >= key,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Linear lower_bound with loop invariant carrying sortedness */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            binary_search_precond(a, key),
            forall|j: int| 0 <= j < i as int ==> a[j] < key,
        decreases a.len() - i
    {
        let v = a[i];
        if v >= key {
            proof {
                assert_forall_by(|j: int| {
                    requires(i as int <= j && j < a.len() as int);
                    ensures(a[j] >= key);
                    assert(0 <= i as int);
                    assert(i as int <= j);
                    assert(j < a.len() as int);
                    assert(binary_search_precond(a, key));
                    assert(a[i as int] <= a[j]);
                    assert(a[i as int] == v);
                    assert(v <= a[j]);
                    assert(v >= key);
                    assert(key <= a[j]);
                    assert(a[j] >= key);
                });
            }
            return i;
        }
        proof { assert(v < key); }
        i = i + 1;
    }
    i
}
// </vc-code>

}
fn main() {}