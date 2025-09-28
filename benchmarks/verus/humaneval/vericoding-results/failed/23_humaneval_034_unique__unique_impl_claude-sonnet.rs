// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed len() call by using .len() spec function */
fn sort_vec(mut v: Vec<i8>) -> (result: Vec<i8>)
    ensures
        v@.len() == result@.len(),
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> (result@[i] as int) <= (result@[j] as int),
        forall|x: i8| v@.contains(x) <==> result@.contains(x)
{
    let original_len = v.len();
    let original_seq = v@;
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|k: int, l: int| 0 <= k < l < i ==> (v@[k] as int) <= (v@[l] as int),
            v.len() == original_len,
            forall|x: i8| original_seq.contains(x) <==> v@.contains(x)
    {
        let mut j = i;
        while j > 0 && v[j - 1] > v[j]
            invariant
                0 <= j <= i < v.len(),
                forall|k: int, l: int| 0 <= k < l < j ==> (v@[k] as int) <= (v@[l] as int),
                forall|k: int, l: int| j < k < l <= i ==> (v@[k] as int) <= (v@[l] as int),
                v.len() == original_len,
                forall|x: i8| original_seq.contains(x) <==> v@.contains(x)
        {
            let temp = v[j];
            v.set(j, v[j - 1]);
            v.set(j - 1, temp);
            j -= 1;
        }
        i += 1;
    }
    v
}

fn remove_duplicates(v: Vec<i8>) -> (result: Vec<i8>)
    requires
        forall|i: int, j: int| 0 <= i < j < v@.len() ==> (v@[i] as int) <= (v@[j] as int)
    ensures
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> (result@[i] as int) < (result@[j] as int),
        forall|x: i8| result@.contains(x) ==> v@.contains(x),
        forall|x: i8| v@.contains(x) ==> result@.contains(x)
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|k: int, l: int| 0 <= k < l < result@.len() ==> (result@[k] as int) < (result@[l] as int),
            forall|x: i8| result@.contains(x) ==> v@.contains(x),
            forall|j: int| 0 <= j < i ==> v@.contains(v@[j]) ==> result@.contains(v@[j])
    {
        if result.len() == 0 || result[result.len() - 1] != v[i] {
            result.push(v[i]);
        }
        i += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn unique(s: Vec<i8>) -> (result: Vec<i8>)
    ensures
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> (result@[i] as int) < (result@[j] as int) &&
        forall|x: i8| result@.contains(x) ==> s@.contains(x) &&
        forall|x: i8| s@.contains(x) ==> result@.contains(x)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): using helper functions for unique implementation */
    let sorted = sort_vec(s);
    let result = remove_duplicates(sorted);
    result
}
// </vc-code>


}

fn main() {}