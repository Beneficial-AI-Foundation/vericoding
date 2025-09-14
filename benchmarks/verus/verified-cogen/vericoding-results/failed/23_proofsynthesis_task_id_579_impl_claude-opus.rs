// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn contains_unique(s: Seq<i32>, v: i32, idx: int) -> bool {
    0 <= idx < s.len() && s[idx] == v && forall|j: int| 0 <= j < idx ==> s[j] != v
}

/* helper modified by LLM (iteration 5): fixed ghost sequence access in proof */
proof fn lemma_push_maintains_no_duplicates(s: Seq<i32>, v: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j],
        !s.contains(v),
    ensures
        forall|i: int, j: int| 0 <= i < j < s.push(v).len() ==> s.push(v)[i] != s.push(v)[j],
{
    assert forall|i: int, j: int| 0 <= i < j < s.push(v).len() implies s.push(v)[i] != s.push(v)[j] by {
        if j == s.len() {
            assert(s.push(v)[j] == v);
            if i < s.len() {
                assert(s.push(v)[i] == s[i]);
                assert(!s.contains(v));
            }
        } else {
            assert(s.push(v)[i] == s[i]);
            assert(s.push(v)[j] == s[j]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)

    ensures
        forall|i: int|
            0 <= i < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(
                arr1[i],
            )),
        forall|i: int|
            0 <= i < arr2.len() ==> (!arr1@.contains(#[trigger] arr2[i]) ==> result@.contains(
                arr2[i],
            )),
        forall|i: int, j: int|
            0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed sequence indexing syntax */
    let mut result = Vec::new();
    let ghost mut result_ghost = Seq::<i32>::empty();
    
    let mut i = 0;
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            result@ == result_ghost,
            forall|k: int| 0 <= k < i && !arr2@.contains(arr1@[k]) ==> result_ghost.contains(arr1@[k]),
            forall|k: int, j: int| 0 <= k < j < result_ghost.len() ==> result_ghost[k] != result_ghost[j],
    {
        if !arr2@.contains(arr1[i]) && !result@.contains(arr1[i]) {
            proof {
                lemma_push_maintains_no_duplicates(result_ghost, arr1@[i as int]);
            }
            result.push(arr1[i]);
            proof {
                result_ghost = result_ghost.push(arr1@[i as int]);
            }
        }
        i = i + 1;
    }
    
    let mut j = 0;
    while j < arr2.len()
        invariant
            0 <= j <= arr2.len(),
            result@ == result_ghost,
            forall|k: int| 0 <= k < arr1.len() && !arr2@.contains(arr1@[k]) ==> result_ghost.contains(arr1@[k]),
            forall|k: int| 0 <= k < j && !arr1@.contains(arr2@[k]) ==> result_ghost.contains(arr2@[k]),
            forall|k: int, m: int| 0 <= k < m < result_ghost.len() ==> result_ghost[k] != result_ghost[m],
    {
        if !arr1@.contains(arr2[j]) && !result@.contains(arr2[j]) {
            proof {
                lemma_push_maintains_no_duplicates(result_ghost, arr2@[j as int]);
            }
            result.push(arr2[j]);
            proof {
                result_ghost = result_ghost.push(arr2@[j as int]);
            }
        }
        j = j + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}