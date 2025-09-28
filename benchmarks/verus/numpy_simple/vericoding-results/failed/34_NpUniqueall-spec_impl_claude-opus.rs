// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn contains(s: Seq<i8>, v: i8) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == v
}

/* helper modified by LLM (iteration 2): Added decreases clauses to proof lemmas */
proof fn lemma_contains_after_push(s: Seq<i8>, v: i8, elem: i8)
    requires
        contains(s, v),
    ensures
        contains(s.push(elem), v),
{
    let witness_i = choose|i: int| 0 <= i < s.len() && s[i] == v;
    assert(s.push(elem)[witness_i] == v);
}

proof fn lemma_push_maintains_uniqueness(s: Seq<i8>, v: i8)
    requires
        forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < i ==> s[i] != s[j],
        !contains(s, v),
    ensures
        forall|i: int, j: int| 0 <= i < s.push(v).len() && 0 <= j < i ==> s.push(v)[i] != s.push(v)[j],
{
    assert forall|i: int, j: int| 0 <= i < s.push(v).len() && 0 <= j < i implies s.push(v)[i] != s.push(v)[j] by {
        if i == s.len() {
            assert(s.push(v)[i] == v);
            if j < s.len() {
                assert(s.push(v)[j] == s[j]);
                assert(!contains(s, v));
            }
        } else {
            assert(s.push(v)[i] == s[i]);
            if j < s.len() {
                assert(s.push(v)[j] == s[j]);
            }
        }
    }
}

proof fn lemma_all_elements_represented(arr: Seq<i8>, result: Seq<i8>, i: int)
    requires
        0 <= i <= arr.len(),
        forall|k: int| 0 <= k < i ==> exists|j: int| 0 <= j < result.len() && result[j] == arr[k],
        contains(result, arr[i]),
    ensures
        forall|k: int| 0 <= k <= i ==> exists|j: int| 0 <= j < result.len() && result[j] == arr[k],
{
}
// </vc-helpers>

// <vc-spec>
fn unique_all(arr: Vec<i8>) -> (ret: Vec<i8>)
    ensures
        ret.len() <= arr.len(),
        forall|i: int| 0 <= i < arr@.len() ==> exists|j: int| 0 <= j < ret@.len() && ret@[j] == #[trigger] arr@[i],
        forall|i: int, j: int| 0 <= i < ret@.len() && 0 <= j < i ==> ret@[i] != ret@[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clauses to both while loops */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@.len() <= i,
            forall|k: int| 0 <= k < i ==> exists|j: int| 0 <= j < result@.len() && result@[j] == arr@[k],
            forall|k: int, j: int| 0 <= k < result@.len() && 0 <= j < k ==> result@[k] != result@[j],
        decreases arr.len() - i
    {
        let elem = arr[i];
        let mut found = false;
        let mut j: usize = 0;
        
        while j < result.len()
            invariant
                j <= result.len(),
                found ==> exists|k: int| 0 <= k < j && result@[k] == elem,
                !found ==> forall|k: int| 0 <= k < j ==> result@[k] != elem,
            decreases result.len() - j
        {
            if result[j] == elem {
                found = true;
                proof {
                    assert(result@[j as int] == elem);
                }
            }
            j = j + 1;
        }
        
        if !found {
            proof {
                assert(!contains(result@, elem));
                lemma_push_maintains_uniqueness(result@, elem);
            }
            result.push(elem);
        } else {
            proof {
                assert(contains(result@, elem));
                lemma_all_elements_represented(arr@, result@, i as int);
            }
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}